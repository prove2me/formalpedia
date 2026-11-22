-- Prove2me | solution 1 for MasulloGRH.exists_linear_lift_of_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T17:25:25.075458+00:00
-- url     : https://prove2.me/submissions/c3f4e809-6e3e-4327-8de0-abdefd673184

import Definitions.Def_MasulloGRH_SchwartzBruhat
import Theorems.Thm_MasulloGRH_closedAddSubgroup_eq_submodule_add_countable
import Theorems.Thm_MasulloGRH_isCompact_preimage_of_isOpenMap_of_isCompact_ker

set_option autoImplicit false

open Topology Filter MeasureTheory

namespace MasulloGRHLiftAux

open MasulloGRH

/-- the covering of the identity component -/
def ℒ {m n r s : ℕ} {d : Fin s → ℕ} (y : (Fin m → ℝ) × (Fin n → ℝ)) : ElemGroup m n r s d :=
  (y.1, fun j => ((y.2 j : ℝ) : UnitAddCircle), 0, 0)

section
variable {m n r s : ℕ} {d : Fin s → ℕ}

lemma ℒ_zero : (ℒ (0 : (Fin m → ℝ) × (Fin n → ℝ)) : ElemGroup m n r s d) = 0 := by
  ext <;> simp [ℒ]

lemma ℒ_add (y z : (Fin m → ℝ) × (Fin n → ℝ)) :
    (ℒ (y + z) : ElemGroup m n r s d) = ℒ y + ℒ z := by
  ext <;> simp [ℒ, AddCircle.coe_add]

lemma ℒ_neg (y : (Fin m → ℝ) × (Fin n → ℝ)) :
    (ℒ (-y) : ElemGroup m n r s d) = -ℒ y := by
  ext <;> simp [ℒ, AddCircle.coe_neg]

lemma continuous_ℒ : Continuous (ℒ : (Fin m → ℝ) × (Fin n → ℝ) → ElemGroup m n r s d) := by
  have h : Continuous (fun x : ℝ => (x : UnitAddCircle)) := AddCircle.continuous_mk' 1
  unfold ℒ
  fun_prop

/-- an open subgroup contains the identity component -/
lemma mem_of_isOpen (H : Subgroup (Multiplicative (ElemGroup m n r s d)))
    (hH : IsOpen (H : Set (Multiplicative (ElemGroup m n r s d))))
    (y : (Fin m → ℝ) × (Fin n → ℝ)) : Multiplicative.ofAdd (ℒ y) ∈ H := by
  let S : AddSubgroup ((Fin m → ℝ) × (Fin n → ℝ)) :=
    { carrier := {y | Multiplicative.ofAdd (ℒ y : ElemGroup m n r s d) ∈ H}
      zero_mem' := by simp only [Set.mem_ofPred_eq, ℒ_zero, ofAdd_zero]; exact H.one_mem
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, ℒ_add, ofAdd_add] at *; exact H.mul_mem ha hb
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, ℒ_neg, ofAdd_neg] at *; exact H.inv_mem ha }
  have hSo : IsOpen (S : Set ((Fin m → ℝ) × (Fin n → ℝ))) :=
    hH.preimage (continuous_ofAdd.comp continuous_ℒ)
  have hSc := AddSubgroup.isClosed_of_isOpen S hSo
  have := (convex_univ (𝕜 := ℝ)).isPreconnected.subset_isClopen ⟨hSc, hSo⟩
    ⟨0, Set.mem_univ _, S.zero_mem⟩ (Set.mem_univ y)
  exact this

end

section main

variable (P : Type*) [CommGroup P] [TopologicalSpace P] [IsTopologicalGroup P] [T2Space P]
    [LocallyCompactSpace P] (P₀ : Subgroup P) (hP₀ : IsOpen (P₀ : Set P))
    (m n r s : ℕ) (d : Fin s → ℕ)
    (α : ↥P₀ →* Multiplicative (ElemGroup m n r s d)) (hαc : Continuous α) (hαo : IsOpenMap α)
    (hαk : IsCompact {x : ↥P₀ | α x = 1})
    (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
    (β : P →* Multiplicative (ElemGroup m' n' r' s' d')) (hβc : Continuous β)
    (hβo : IsOpenMap β)

include hP₀ hαc hβo in
/-- every element of the identity component of `E'` is `β q` with `α q` in the identity
component of `E` -/
lemma exists_of_identity (y' : (Fin m' → ℝ) × (Fin n' → ℝ)) :
    ∃ q : P₀, (Multiplicative.toAdd (α q)).2.2 = 0 ∧ β q = Multiplicative.ofAdd (ℒ y') := by
  let E₀ : Subgroup (Multiplicative (ElemGroup m n r s d)) :=
    { carrier := {x | (Multiplicative.toAdd x).2.2 = 0}
      one_mem' := rfl
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, toAdd_mul, Prod.snd_add] at *; rw [ha, hb, add_zero]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, toAdd_inv, Prod.snd_neg] at *; rw [ha, neg_zero] }
  have hE₀ : IsOpen (E₀ : Set (Multiplicative (ElemGroup m n r s d))) :=
    (isOpen_discrete {(0 : (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)))}).preimage
      ((continuous_snd.comp continuous_snd).comp continuous_toAdd)
  let Q := E₀.comap α
  have hQ : IsOpen (Q : Set P₀) := hE₀.preimage hαc
  let H := Q.map (β.comp P₀.subtype)
  have hH : IsOpen (H : Set (Multiplicative (ElemGroup m' n' r' s' d'))) := by
    have : (H : Set _) = β '' (Subtype.val '' (Q : Set P₀)) := by
      ext x; simp [H, Subgroup.coe_map, Set.mem_image]
    rw [this]
    exact hβo _ (hP₀.isOpenMap_subtype_val _ hQ)
  obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.1 (mem_of_isOpen H hH y')
  exact ⟨q, hq, hqe⟩

/-- the lifted graph of the correspondence -/
def V : AddSubgroup (((Fin m → ℝ) × (Fin n → ℝ)) × ((Fin m' → ℝ) × (Fin n' → ℝ))) where
  carrier := {z | ∃ p : P₀, α p = Multiplicative.ofAdd (ℒ z.1) ∧ β p = Multiplicative.ofAdd (ℒ z.2)}
  zero_mem' := ⟨1, by simp [ℒ_zero], by simp [ℒ_zero]⟩
  add_mem' := fun {a b} ⟨p, hp1, hp2⟩ ⟨q, hq1, hq2⟩ =>
    ⟨p * q, by simp [hp1, hq1, ℒ_add], by simp [hp2, hq2, ℒ_add]⟩
  neg_mem' := fun {a} ⟨p, hp1, hp2⟩ => ⟨p⁻¹, by simp [hp1, ℒ_neg], by simp [hp2, ℒ_neg]⟩

include hP₀ hαc hαo hαk hβc in
lemma isClosed_V : IsClosed ((V P P₀ m n r s d α m' n' r' s' d' β : AddSubgroup _) :
    Set (((Fin m → ℝ) × (Fin n → ℝ)) × ((Fin m' → ℝ) × (Fin n' → ℝ)))) := by
  haveI : T2Space (Multiplicative (ElemGroup m n r s d)) :=
    inferInstanceAs (T2Space (ElemGroup m n r s d))
  haveI : T2Space (Multiplicative (ElemGroup m' n' r' s' d')) :=
    inferInstanceAs (T2Space (ElemGroup m' n' r' s' d'))
  haveI : LocallyCompactSpace P₀ := hP₀.locallyCompactSpace
  refine isClosed_of_closure_subset fun z hz => ?_
  obtain ⟨zs, hzs, hlim⟩ := mem_closure_iff_seq_limit.1 hz
  choose ps hps1 hps2 using hzs
  obtain ⟨N, hNc, hNn⟩ := exists_compact_mem_nhds (ℒ z.1 : ElemGroup m n r s d)
  have hKc : IsCompact (α ⁻¹' (Multiplicative.ofAdd '' N)) :=
    isCompact_preimage_of_isOpenMap_of_isCompact_ker α hαc hαo hαk (hNc.image continuous_ofAdd)
  have h1 : Tendsto (fun i => (ℒ (zs i).1 : ElemGroup m n r s d)) atTop (𝓝 (ℒ z.1)) :=
    (continuous_ℒ.tendsto _).comp ((continuous_fst.tendsto _).comp hlim)
  have h2 : Tendsto (fun i => (ℒ (zs i).2 : ElemGroup m' n' r' s' d')) atTop (𝓝 (ℒ z.2)) :=
    (continuous_ℒ.tendsto _).comp ((continuous_snd.tendsto _).comp hlim)
  have hev : ∀ᶠ i in atTop, ps i ∈ α ⁻¹' (Multiplicative.ofAdd '' N) := by
    filter_upwards [h1 hNn] with i hi
    exact ⟨_, hi, (hps1 i).symm⟩
  obtain ⟨p, -, hp⟩ := hKc.exists_mapClusterPt (le_principal_iff.2 hev)
  have hα : MapClusterPt (α p) atTop (α ∘ ps) := hp.tendsto_comp (hαc.tendsto p)
  have hβ : MapClusterPt (β p) atTop ((β ∘ Subtype.val) ∘ ps) :=
    hp.tendsto_comp ((hβc.comp continuous_subtype_val).tendsto p)
  have hαe : α ∘ ps = Multiplicative.ofAdd ∘ fun i => (ℒ (zs i).1 : ElemGroup m n r s d) :=
    funext hps1
  have hβe : (β ∘ Subtype.val) ∘ ps =
      Multiplicative.ofAdd ∘ fun i => (ℒ (zs i).2 : ElemGroup m' n' r' s' d') := funext hps2
  rw [hαe] at hα
  rw [hβe] at hβ
  have e1 : α p = Multiplicative.ofAdd (ℒ z.1) :=
    eq_of_nhds_neBot (hα.neBot.mono (inf_le_inf_left _
      (((continuous_ofAdd.tendsto _).comp h1))))
  have e2 : β p = Multiplicative.ofAdd (ℒ z.2) :=
    eq_of_nhds_neBot (hβ.neBot.mono (inf_le_inf_left _
      (((continuous_ofAdd.tendsto _).comp h2))))
  exact ⟨p, e1, e2⟩

include hP₀ hαc hαo hαk hβc hβo in
theorem exists_lift :
    ∃ Λ : ((Fin m' → ℝ) × (Fin n' → ℝ)) →ₗ[ℝ] ((Fin m → ℝ) × (Fin n → ℝ)),
      ∀ y', ∃ p : P₀, α p = Multiplicative.ofAdd (ℒ (Λ y')) ∧
        β p = Multiplicative.ofAdd (ℒ y') := by
  obtain ⟨W, hWV, D, hDc, -, hdec⟩ := closedAddSubgroup_eq_submodule_add_countable
    (V P P₀ m n r s d α m' n' r' s' d' β) (isClosed_V P P₀ hP₀ m n r s d α hαc hαo hαk m' n' r' s' d' β hβc)
  have hsurj : ∀ y' : (Fin m' → ℝ) × (Fin n' → ℝ),
      ∃ z ∈ V P P₀ m n r s d α m' n' r' s' d' β, z.2 = y' := by
    intro y'
    obtain ⟨q, hq, hqe⟩ := exists_of_identity P P₀ hP₀ m n r s d α hαc m' n' r' s' d' β hβo y'
    refine ⟨(((Multiplicative.toAdd (α q)).1, fun j => ((Multiplicative.toAdd (α q)).2.1 j).out), y'),
      ⟨q, ?_, hqe⟩, rfl⟩
    show α q = Multiplicative.ofAdd (ℒ _)
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    have h2 := hq
    ext
    · rfl
    · simp only [ℒ]
      exact (QuotientAddGroup.out_eq' _).symm
    · simp only [ℒ]; rw [congrArg Prod.fst h2]; rfl
    · simp only [ℒ]; rw [congrArg Prod.snd h2]; rfl
  let f := (LinearMap.snd ℝ ((Fin m → ℝ) × (Fin n → ℝ)) ((Fin m' → ℝ) × (Fin n' → ℝ))).comp
    W.subtype
  have hrange : LinearMap.range f = ⊤ := by
    by_contra hne
    let μ : Measure ((Fin m' → ℝ) × (Fin n' → ℝ)) := Measure.addHaar
    have h0 : μ (LinearMap.range f : Set _) = 0 := Measure.addHaar_submodule μ _ hne
    have hcov : (Set.univ : Set ((Fin m' → ℝ) × (Fin n' → ℝ))) ⊆
        ⋃ δ ∈ D, (fun x => -δ.2 + x) ⁻¹' (LinearMap.range f : Set _) := by
      intro y' _
      obtain ⟨z, hz, rfl⟩ := hsurj y'
      obtain ⟨w, hw, δ, hδ, rfl⟩ := hdec z hz
      refine Set.mem_iUnion₂.2 ⟨δ, hδ, ⟨⟨w, hw⟩, ?_⟩⟩
      simp [f]
    have : μ Set.univ = 0 := measure_mono_null hcov
      ((measure_biUnion_null_iff hDc).2 fun δ _ => by rw [measure_preimage_add]; exact h0)
    exact (Measure.measure_univ_ne_zero.2 (NeZero.ne μ)) this
  obtain ⟨σ, hσ⟩ := f.exists_rightInverse_of_surjective hrange
  refine ⟨(LinearMap.fst ℝ _ _).comp (W.subtype.comp σ), fun y' => ?_⟩
  have h2 : ((σ y' : W) : ((Fin m → ℝ) × (Fin n → ℝ)) × ((Fin m' → ℝ) × (Fin n' → ℝ))).2 = y' :=
    LinearMap.congr_fun hσ y'
  obtain ⟨p, hp1, hp2⟩ := hWV (σ y').2
  refine ⟨p, hp1, ?_⟩
  rw [hp2, h2]

end main

end MasulloGRHLiftAux

open MasulloGRH in
theorem solution
    (P : Type*) [CommGroup P] [TopologicalSpace P] [IsTopologicalGroup P] [T2Space P]
    [LocallyCompactSpace P] (P₀ : Subgroup P) (hP₀ : IsOpen (P₀ : Set P))
    (m n r s : ℕ) (d : Fin s → ℕ)
    (α : ↥P₀ →* Multiplicative (ElemGroup m n r s d)) (hαc : Continuous α) (hαo : IsOpenMap α)
    (hαk : IsCompact {x : ↥P₀ | α x = 1})
    (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
    (β : P →* Multiplicative (ElemGroup m' n' r' s' d')) (hβc : Continuous β)
    (hβo : IsOpenMap β) :
    ∃ Λ : ((Fin m' → ℝ) × (Fin n' → ℝ)) →ₗ[ℝ] ((Fin m → ℝ) × (Fin n → ℝ)),
      ∀ y' : (Fin m' → ℝ) × (Fin n' → ℝ), ∃ p : P₀,
        α p = Multiplicative.ofAdd ((Λ y').1, fun j => (((Λ y').2 j : ℝ) : UnitAddCircle), 0, 0) ∧
        β p = Multiplicative.ofAdd (y'.1, fun j => ((y'.2 j : ℝ) : UnitAddCircle), 0, 0) :=
  MasulloGRHLiftAux.exists_lift P P₀ hP₀ m n r s d α hαc hαo hαk m' n' r' s' d' β hβc hβo
