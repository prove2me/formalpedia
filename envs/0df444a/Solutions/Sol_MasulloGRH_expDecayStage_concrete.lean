-- Prove2me | solution 1 for MasulloGRH.expDecayStage_concrete
-- status  : ACCEPTED   (prove)
-- author  : @kirisame
-- created : 2026-11-21T18:59:48.820354+00:00
-- url     : https://prove2.me/submissions/0ace6540-d5cc-41d4-992c-7882a3730a5e

import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Theorems.Thm_MasulloGRH_isCompact_moduleKernel_and_compact_le
import Theorems.Thm_MasulloGRH_schwartzBruhatAverage_transfer
import Theorems.Thm_MasulloGRH_schwartz_correspondence
import Theorems.Thm_MasulloGRH_annihilator_isCompactlyGenerated
import Theorems.Thm_MasulloGRH_exists_elemPresentation_of_isStructuralPair
import Theorems.Thm_MasulloGRH_schwartzBruhat_main_structure
import Theorems.Thm_MasulloGRH_nuclear_of_projective_topology
import Theorems.Thm_MasulloGRH_elemSchwartz_frechet_nuclear_montel
import Definitions.Def_MasulloGRH_ExpDecayStages

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

namespace MasulloGRHStageConcreteAux

open MasulloGRH MeasureTheory Topology Filter

/-! ### Continuity of Schwartz–Bruhat functions -/

theorem continuous_of_isRapidDecay {m n r s : ℕ} {d : Fin s → ℕ}
    (g : ElemGroup m n r s d → ℂ) (hg : IsRapidDecay g) : Continuous g := by
  let q : (Fin m → ℝ) × ((Fin n → ℝ) × ((Fin r → ℤ) × ((i : Fin s) → ZMod (d i)))) →
      ElemGroup m n r s d :=
    Prod.map id (Prod.map (Pi.map fun _ (t : ℝ) => (t : UnitAddCircle)) id)
  have hqc : Continuous q := by
    refine continuous_id.prodMap (Continuous.prodMap ?_ continuous_id)
    exact continuous_pi fun j => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply j)
  have hqo : IsOpenMap q := by
    refine IsOpenMap.id.prodMap (IsOpenMap.prodMap ?_ IsOpenMap.id)
    exact IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe) (Filter.Eventually.of_forall
      fun _ => QuotientAddGroup.mk_surjective)
  have hqs : Function.Surjective q := by
    refine Function.Surjective.prodMap Function.surjective_id
      (Function.Surjective.prodMap ?_ Function.surjective_id)
    intro z
    exact ⟨fun j => (QuotientAddGroup.mk_surjective (z j)).choose,
      funext fun j => (QuotientAddGroup.mk_surjective (z j)).choose_spec⟩
  have hq : Topology.IsQuotientMap q := hqo.isQuotientMap hqc hqs
  rw [hq.continuous_iff]
  let h : ((Fin r → ℤ) × ((i : Fin s) → ZMod (d i))) × ((Fin m → ℝ) × (Fin n → ℝ)) → ℂ :=
    fun p => elemLift g p.1.1 p.1.2 p.2
  have hh : Continuous h := by
    rw [continuous_prod_of_discrete_left]
    intro ab
    exact (hg.1 ab.1 ab.2).continuous
  have : g ∘ q = h ∘ fun p => (p.2.2, (p.1, p.2.1)) := rfl
  rw [this]
  exact hh.comp (by fun_prop)

theorem continuous_elemSchwartz {m n r s : ℕ} {d : Fin s → ℕ} (g : ElemSchwartz m n r s d) :
    Continuous g.toFun := by
  obtain ⟨g, hg⟩ := g
  show Continuous g
  induction hg using Submodule.span_induction with
  | mem x hx => exact continuous_of_isRapidDecay x hx
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

section group

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_extendPullback {m n r s : ℕ} {d : Fin s → ℕ} (Γ : Subgroup G)
    (hΓ : IsOpen (Γ : Set G)) (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hπ : Continuous π)
    (g : ElemGroup m n r s d → ℂ) (hg : Continuous g) : Continuous (extendPullback Γ π g) := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Γ
  · have hon : ContinuousOn (extendPullback Γ π g) (Γ : Set G) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : (Set.domRestrict (Γ : Set G) (extendPullback Γ π g)) =
          fun y : Γ => g (Multiplicative.toAdd (π y)) := by
        funext y
        simp [Set.domRestrict, extendPullback]
      rw [this]
      exact hg.comp (continuous_toAdd.comp hπ)
    exact hon.continuousAt (hΓ.mem_nhds hx)
  · have hcl : IsOpen ((Γ : Set G)ᶜ) := (Subgroup.isClosed_of_isOpen Γ hΓ).isOpen_compl
    refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [hcl.mem_nhds hx] with y hy
    simp [extendPullback, show y ∉ Γ from hy]

theorem continuous_of_mem_schwartzBruhatSubmodule (f : G → ℂ)
    (hf : f ∈ schwartzBruhatSubmodule G) : Continuous f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hx
    exact continuous_extendPullback Γ hs.1 π hπ.2.1 _ (continuous_elemSchwartz g)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

/-! ### Averaging -/

local instance instMeasurableSpaceSubgroup (k : Subgroup G) : MeasurableSpace k := borel k
local instance instBorelSpaceSubgroup (k : Subgroup G) : BorelSpace k := ⟨rfl⟩

theorem subgroupHaar_eq (k : Subgroup G) (hk : IsCompact (k : Set G)) :
    haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
    subgroupHaar k = Measure.haarMeasure ⊤ := by
  simp only [subgroupHaar, dif_pos hk]

theorem isProbabilityMeasure_subgroupHaar (k : Subgroup G) (hk : IsCompact (k : Set G)) :
    IsProbabilityMeasure (subgroupHaar k) := by
  have : CompactSpace k := isCompact_iff_compactSpace.mp hk
  rw [subgroupHaar_eq k hk]
  constructor
  have := Measure.haarMeasure_self (G := k) (K₀ := ⊤)
  simpa using this

open Classical in
theorem average_apply (Γ k : Subgroup G) (f : G → ℂ) (x : G) :
    schwartzBruhatAverage Γ k f x =
      if x ∈ Γ then ∫ y : k, f (x * y) ∂subgroupHaar k else 0 := by
  classical
  simp only [schwartzBruhatAverage, Set.indicator_apply, SetLike.mem_coe]

theorem integrable_translate (k : Subgroup G) (hk : IsCompact (k : Set G)) (f : G → ℂ)
    (hf : Continuous f) (x : G) :
    Integrable (fun y : k => f (x * y)) (subgroupHaar k) := by
  have := isProbabilityMeasure_subgroupHaar k hk
  have : CompactSpace k := isCompact_iff_compactSpace.mp hk
  have hc : Continuous (fun y : k => f (x * y)) :=
    hf.comp (continuous_const.mul continuous_subtype_val)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem average_add (Γ k : Subgroup G) (hk : IsCompact (k : Set G)) (f g : G → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    schwartzBruhatAverage Γ k (f + g) =
      schwartzBruhatAverage Γ k f + schwartzBruhatAverage Γ k g := by
  funext x
  simp only [average_apply, Pi.add_apply]
  split_ifs
  · exact integral_add (integrable_translate k hk f hf x) (integrable_translate k hk g hg x)
  · simp

theorem average_smul (Γ k : Subgroup G) (c : ℂ) (f : G → ℂ) :
    schwartzBruhatAverage Γ k (c • f) = c • schwartzBruhatAverage Γ k f := by
  funext x
  simp only [average_apply, Pi.smul_apply]
  split_ifs
  · exact integral_smul c _
  · simp

theorem average_zero (Γ k : Subgroup G) :
    schwartzBruhatAverage Γ k (0 : G → ℂ) = 0 := by
  funext x
  simp [average_apply]

theorem extendPullback_zero {m n r s : ℕ} {d : Fin s → ℕ} (Γ : Subgroup G)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) :
    extendPullback Γ π (0 : ElemGroup m n r s d → ℂ) = 0 := by
  funext x
  simp [extendPullback]

theorem extendPullback_add {m n r s : ℕ} {d : Fin s → ℕ} (Γ : Subgroup G)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (g₁ g₂ : ElemGroup m n r s d → ℂ) :
    extendPullback Γ π (g₁ + g₂) = extendPullback Γ π g₁ + extendPullback Γ π g₂ := by
  funext x
  by_cases hx : x ∈ Γ <;> simp [extendPullback, hx]

theorem extendPullback_smul {m n r s : ℕ} {d : Fin s → ℕ} (Γ : Subgroup G)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (c : ℂ) (g : ElemGroup m n r s d → ℂ) :
    extendPullback Γ π (c • g) = c • extendPullback Γ π g := by
  funext x
  by_cases hx : x ∈ Γ <;> simp [extendPullback, hx]

lemma extendPullback_mul {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (g : ElemGroup m n r s d → ℂ) (x y : G) (hy : y ∈ k) :
    extendPullback Γ π g (x * y) = extendPullback Γ π g x := by
  have hyΓ : y ∈ Γ := hs.2.2.2 hy
  unfold extendPullback
  by_cases hx : x ∈ Γ
  · have hxy : x * y ∈ Γ := Γ.mul_mem hx hyΓ
    rw [dif_pos hxy, dif_pos hx]
    have h1 : π ⟨y, hyΓ⟩ = 1 := (hπ.2.2.2.2 ⟨y, hyΓ⟩).2 hy
    have : (⟨x * y, hxy⟩ : Γ) = ⟨x, hx⟩ * ⟨y, hyΓ⟩ := rfl
    rw [this, map_mul, h1, mul_one]
  · have hxy : x * y ∉ Γ := fun h => hx (by simpa using Γ.mul_mem h (Γ.inv_mem hyΓ))
    rw [dif_neg hxy, dif_neg hx]

lemma average_eq (k₀ : Subgroup G) (hk₀ : IsCompact (k₀ : Set G)) (f : G → ℂ)
    (hf : ∀ x, ∀ y ∈ k₀, f (x * y) = f x) :
    schwartzBruhatAverage ⊤ k₀ f = f := by
  funext x
  have := isProbabilityMeasure_subgroupHaar k₀ hk₀
  rw [average_apply, if_pos (Subgroup.mem_top x)]
  have h1 : (fun y : k₀ => f (x * y)) = fun _ => f x := funext fun y => hf x y y.2
  rw [h1]
  simp

/-- Descent: a `k`-invariant Schwartz–Bruhat function is a pull-back along a presentation
of `(⊤, k)`. -/
theorem descent [T2Space G] [LocallyCompactSpace G] (k : Subgroup G) {m n r s : ℕ}
    {d : Fin s → ℕ} (π : (⊤ : Subgroup G) →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair ⊤ k) (hπ : IsElemPresentation ⊤ k π) (f : G → ℂ)
    (hf : f ∈ schwartzBruhatSubmodule G) (hinv : ∀ x, ∀ y ∈ k, f (x * y) = f x) :
    ∃ g : ElemSchwartz m n r s d, f = extendPullback ⊤ π g.toFun := by
  have hkc : IsCompact (k : Set G) := isCompact_of_isGoodSubgroup G k hs.2.2.1
  have key : ∀ f ∈ schwartzBruhatSubmodule G, ∃ g : ElemSchwartz m n r s d,
      schwartzBruhatAverage ⊤ k f = extendPullback ⊤ π g.toFun := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Γ, k', m', n', r', s', d', π', g, hs', hπ', rfl⟩ := hx
      obtain ⟨T, -, hT⟩ := schwartzBruhatAverage_transfer G Γ k' m' n' r' s' d' π' hs' hπ'
        ⊤ k m n r s d π hs hπ
      exact ⟨T g, hT g⟩
    | zero => exact ⟨0, by rw [average_zero]; exact (extendPullback_zero _ _).symm⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨g₁, h₁⟩ := ihx
      obtain ⟨g₂, h₂⟩ := ihy
      refine ⟨g₁ + g₂, ?_⟩
      rw [average_add _ _ hkc _ _ (continuous_of_mem_schwartzBruhatSubmodule _ hx)
        (continuous_of_mem_schwartzBruhatSubmodule _ hy), h₁, h₂]
      exact (extendPullback_add _ _ _ _).symm
    | smul c x hx ihx =>
      obtain ⟨g, h⟩ := ihx
      refine ⟨c • g, ?_⟩
      rw [average_smul, h]
      exact (extendPullback_smul _ _ _ _).symm
  obtain ⟨g, hg⟩ := key f hf
  exact ⟨g, by rw [← hg, average_eq k hkc f hinv]⟩

end group

/-! ### The explicit equivalence for a minimal good subgroup -/

lemma ws_all {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] {ι : Type*} {p : SeminormFamily ℂ E ι} (hp : WithSeminorms p) :
    WithSeminorms (fun q : {q : Seminorm ℂ E // Continuous q} => q.1) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
  refine le_antisymm (le_iInf fun q => ?_) ?_
  · rw [← tendsto_iff_comap]
    have := q.2.tendsto 0
    rwa [map_zero] at this
  · rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf p).1 hp]
    exact le_iInf fun i => iInf_le_of_le ⟨p i, hp.continuous_seminorm i⟩ le_rfl

section single

variable {H : Type u} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- the inclusion of a structural pair, as a linear map -/
noncomputable def ofElemL {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup H)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : ElemSchwartz m n r s d →ₗ[ℂ] SchwartzBruhat H where
  toFun := SchwartzBruhat.ofElem Γ k π hs hπ
  map_add' f g := by
    apply Subtype.ext
    funext x
    show extendPullback Γ π (f + g).toFun x = extendPullback Γ π f.toFun x + extendPullback Γ π g.toFun x
    unfold extendPullback
    split_ifs
    · rfl
    · simp
  map_smul' c f := by
    apply Subtype.ext
    funext x
    show extendPullback Γ π (c • f).toFun x = c * extendPullback Γ π f.toFun x
    unfold extendPullback
    split_ifs
    · rfl
    · simp

lemma ofElem_continuous {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup H)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : Continuous (SchwartzBruhat.ofElem Γ k π hs hπ) :=
  continuous_sInf_rng.2 fun _ ht => ht.2 Γ k m n r s d π hs hπ

lemma ofElem_injective {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup H)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : Function.Injective (SchwartzBruhat.ofElem Γ k π hs hπ) := by
  intro g g' h
  have h' := congrArg Subtype.val h
  apply Subtype.ext
  funext e
  obtain ⟨x, hx⟩ := hπ.2.2.2.1 (Multiplicative.ofAdd e)
  have := congrFun h' (x : H)
  simp only [SchwartzBruhat.ofElem, extendPullback, dif_pos x.2] at this
  rw [Subtype.coe_eta, hx, toAdd_ofAdd] at this
  exact this

theorem equiv_single (Γ₀ k₀ : Subgroup H) (m n r s : ℕ) (d : Fin s → ℕ)
    (π₀ : Γ₀ →* Multiplicative (ElemGroup m n r s d)) (hs₀ : IsStructuralPair Γ₀ k₀)
    (hπ₀ : IsElemPresentation Γ₀ k₀ π₀)
    (hfac : ∀ (Γ k : Subgroup H) (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
      (π : Γ →* Multiplicative (ElemGroup m' n' r' s' d')) (hs : IsStructuralPair Γ k)
      (hπ : IsElemPresentation Γ k π),
      ∃ φ : ElemSchwartz m' n' r' s' d' →ₗ[ℂ] ElemSchwartz m n r s d, Continuous φ ∧
        ∀ g, SchwartzBruhat.ofElem Γ k π hs hπ g = SchwartzBruhat.ofElem Γ₀ k₀ π₀ hs₀ hπ₀ (φ g)) :
    ∃ Φ : ElemSchwartz m n r s d ≃L[ℂ] SchwartzBruhat H,
      ∀ g, Φ g = SchwartzBruhat.ofElem Γ₀ k₀ π₀ hs₀ hπ₀ g := by
  set L := ofElemL Γ₀ k₀ π₀ hs₀ hπ₀ with hL
  have hinj : Function.Injective L := ofElem_injective Γ₀ k₀ π₀ hs₀ hπ₀
  have hsurj : Function.Surjective L := by
    intro f
    have hle : schwartzBruhatSubmodule H ≤
        Submodule.map (schwartzBruhatSubmodule H).subtype (LinearMap.range L) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨Γ, k, m', n', r', s', d', π, g, hs, hπ, rfl⟩
      obtain ⟨φ, -, hφ⟩ := hfac Γ k m' n' r' s' d' π hs hπ
      exact ⟨L (φ g), ⟨φ g, rfl⟩, by
        show (SchwartzBruhat.ofElem Γ₀ k₀ π₀ hs₀ hπ₀ (φ g)).1 = _
        rw [← hφ g]; rfl⟩
    obtain ⟨y, ⟨x, rfl⟩, hy⟩ := hle f.2
    exact ⟨x, Subtype.ext hy⟩
  let e : ElemSchwartz m n r s d ≃ₗ[ℂ] SchwartzBruhat H := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  have he : ∀ y, e y = SchwartzBruhat.ofElem Γ₀ k₀ π₀ hs₀ hπ₀ y := fun y => rfl
  obtain ⟨hFr, -⟩ := elemSchwartz_frechet_nuclear_montel m n r s d hπ₀.1
  have hcont : Continuous e := ofElem_continuous Γ₀ k₀ π₀ hs₀ hπ₀
  have hcont' : Continuous e.symm := by
    obtain ⟨⟨ι, hι, p, hp⟩, -, -⟩ := hFr
    rw [continuous_iff_le_induced]
    letI t : TopologicalSpace (SchwartzBruhat H) :=
      TopologicalSpace.induced e.symm inferInstance
    have hws : WithSeminorms (p.comp (e.symm : SchwartzBruhat H →ₗ[ℂ] ElemSchwartz m n r s d)) :=
      LinearMap.withSeminorms_induced hp _
    haveI : IsTopologicalAddGroup (SchwartzBruhat H) := hws.topologicalAddGroup
    refine sInf_le ⟨⟨_, ⟨⟨0, continuous_const⟩⟩, _, ws_all hws⟩, ?_⟩
    intro Γ k m' n' r' s' d' π hs hπ
    obtain ⟨φ, hφc, hφ⟩ := hfac Γ k m' n' r' s' d' π hs hπ
    refine continuous_induced_rng.2 ?_
    have : (e.symm ∘ SchwartzBruhat.ofElem Γ k π hs hπ) = φ := by
      funext g
      simp only [Function.comp_apply, hφ g, ← he, LinearEquiv.symm_apply_apply]
    rw [this]; exact hφc
  let E : ElemSchwartz m n r s d ≃L[ℂ] SchwartzBruhat H :=
    { e with continuous_toFun := hcont, continuous_invFun := hcont' }
  exact ⟨E, fun g => rfl⟩

theorem equiv_min [T2Space H] [LocallyCompactSpace H]
    (k₀ : Subgroup H) (m n r s : ℕ) (d : Fin s → ℕ)
    (π₀ : (⊤ : Subgroup H) →* Multiplicative (ElemGroup m n r s d))
    (hs₀ : IsStructuralPair ⊤ k₀) (hπ₀ : IsElemPresentation ⊤ k₀ π₀)
    (hmin : ∀ k : Subgroup H, IsGoodSubgroup k → k₀ ≤ k) :
    ∃ Φ : ElemSchwartz m n r s d ≃L[ℂ] SchwartzBruhat H,
      ∀ g, Φ g = SchwartzBruhat.ofElem ⊤ k₀ π₀ hs₀ hπ₀ g := by
  refine equiv_single ⊤ k₀ m n r s d π₀ hs₀ hπ₀ ?_
  intro Γ k m' n' r' s' d' π hs hπ
  have hkc : IsCompact (k : Set H) := isCompact_of_isGoodSubgroup H k hs.2.2.1
  have hk₀c : IsCompact (k₀ : Set H) := isCompact_of_isGoodSubgroup H k₀ hs₀.2.2.1
  let ι : H →* (⊤ : Subgroup H) := Subgroup.topEquiv.symm.toMonoidHom
  have hι : ∀ x, (ι x : H) = x := fun x => rfl
  let β := π₀.comp ι
  have hιc : Continuous ι := continuous_id.subtype_mk _
  have hιo : IsOpenMap ι := by
    intro U hU
    have : ι '' U = Subtype.val ⁻¹' U := by
      ext ⟨x, hx⟩
      constructor
      · rintro ⟨y, hy, hxy⟩
        have := congrArg Subtype.val hxy
        simp only [hι] at this
        subst this; exact hy
      · intro h; exact ⟨x, h, rfl⟩
    rw [this]; exact hU.preimage continuous_subtype_val
  have hβc : Continuous β := hπ₀.2.1.comp hιc
  have hβo : IsOpenMap β := hπ₀.2.2.1.comp hιo
  have hβker : ∀ x, β x = 1 ↔ x ∈ k₀ := fun x => hπ₀.2.2.2.2 (ι x)
  have hβk : IsCompact {x : H | β x = 1} := by
    have : {x : H | β x = 1} = (k₀ : Set H) := Set.ext hβker
    rw [this]; exact hk₀c
  have hαk : IsCompact {x : Γ | π x = 1} := by
    rw [Subtype.isCompact_iff]
    have : (Subtype.val '' {x : Γ | π x = 1}) = (k : Set H) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact (hπ.2.2.2.2 y).1 hy
      · intro hx; exact ⟨⟨x, hs.2.2.2 hx⟩, (hπ.2.2.2.2 _).2 hx, rfl⟩
    rw [this]; exact hkc
  obtain ⟨T, hTc, hT⟩ := schwartz_correspondence H Γ hs.1 m' n' r' s' d' hπ.1 π hπ.2.1
    hπ.2.2.1 hαk m n r s d β hβc hβo hβk
  refine ⟨T, hTc, fun g => ?_⟩
  apply Subtype.ext
  funext x
  show extendPullback Γ π g.toFun x = extendPullback ⊤ π₀ (T g).toFun x
  have hx : x ∈ (⊤ : Subgroup H) := Subgroup.mem_top x
  have e1 : extendPullback ⊤ π₀ (T g).toFun x = (T g).toFun (Multiplicative.toAdd (β x)) := by
    unfold extendPullback; rw [dif_pos hx]; rfl
  rw [e1, (hT g).1 x]
  have hker : β.ker = k₀ := by ext y; exact hβker y
  rw [hker, average_eq k₀ hk₀c _ (fun x y hy =>
    extendPullback_mul Γ k π hs hπ g.toFun x y (hmin k hs.2.2.1 hy))]

end single

/-! ### Modules -/

section modulated

variable {G : Type u} [CommGroup G] [TopologicalSpace G]

lemma m_one {m : G → ℝ} (hm : IsModule m) : m 1 = 1 := by
  have h := hm.map_mul 1 1
  rw [mul_one] at h
  have hp := hm.pos 1
  nlinarith

lemma m_pow {m : G → ℝ} (hm : IsModule m) (g : G) (n : ℕ) : m (g ^ n) = m g ^ n := by
  induction n with
  | zero => simp [m_one hm]
  | succ n ih => rw [pow_succ, hm.map_mul, ih, pow_succ]

lemma m_inv {m : G → ℝ} (hm : IsModule m) (g : G) : m g⁻¹ = (m g)⁻¹ := by
  have h := hm.map_mul g g⁻¹
  rw [mul_inv_cancel, m_one hm] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- the kernel of a module as a subgroup -/
def modKer {m : G → ℝ} (hm : IsModule m) : Subgroup G where
  carrier := {g | m g = 1}
  one_mem' := m_one hm
  mul_mem' {a b} ha hb := by
    show m (a * b) = 1
    rw [hm.map_mul, show m a = 1 from ha, show m b = 1 from hb, one_mul]
  inv_mem' {a} ha := by
    show m a⁻¹ = 1
    rw [m_inv hm, show m a = 1 from ha, inv_one]

lemma top_cg {m : G → ℝ} (hm : IsRposModule m) :
    IsCompactlyGeneratedSubgroup (⊤ : Subgroup G) := by
  have h1 := m_one hm.1
  refine ⟨m ⁻¹' Set.Icc (1/2) 2, hm.1.proper _ _ (by norm_num), fun _ _ => Subgroup.mem_top _,
    ⟨m ⁻¹' Set.Ioo (1/2) 2, (isOpen_Ioo.preimage hm.1.continuous).mem_nhds
      (by simp only [Set.mem_preimage, h1]; constructor <;> norm_num),
      fun x hx => ⟨hx.1.1.le, hx.1.2.le⟩⟩, ?_⟩
  rw [eq_top_iff]
  intro g _
  have ht : 0 < m g := hm.1.pos g
  set n : ℕ := ⌈|Real.log (m g)| / Real.log 2⌉₊ + 1 with hndef
  have hn : (0:ℝ) < n := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : |Real.log (m g) / n| ≤ Real.log 2 := by
    rw [abs_div, abs_of_pos hn, div_le_iff₀ hn]
    have h2 : |Real.log (m g)| / Real.log 2 ≤ n := by
      have := Nat.le_ceil (|Real.log (m g)| / Real.log 2)
      rw [hndef]; push_cast; linarith
    rw [div_le_iff₀ hlog2] at h2
    linarith
  obtain ⟨h, hh⟩ := hm.2 (Real.exp (Real.log (m g) / n)) (Real.exp_pos _)
  have hpow : m (h ^ n) = m g := by
    rw [m_pow hm.1, hh, ← Real.exp_nat_mul, mul_div_cancel₀ _ hn.ne', Real.exp_log ht]
  have hhU : h ∈ m ⁻¹' Set.Icc (1/2) 2 := by
    show m h ∈ Set.Icc (1/2 : ℝ) 2
    rw [hh]
    constructor
    · have : Real.exp (-Real.log 2) ≤ Real.exp (Real.log (m g) / n) :=
        Real.exp_le_exp.2 (neg_le_of_abs_le hb)
      rw [Real.exp_neg, Real.exp_log (by norm_num)] at this
      linarith
    · have : Real.exp (Real.log (m g) / n) ≤ Real.exp (Real.log 2) :=
        Real.exp_le_exp.2 (le_of_abs_le hb)
      rwa [Real.exp_log (by norm_num)] at this
  have hgU : g * (h ^ n)⁻¹ ∈ m ⁻¹' Set.Icc (1/2) 2 := by
    show m (g * (h ^ n)⁻¹) ∈ Set.Icc (1/2 : ℝ) 2
    rw [hm.1.map_mul, m_inv hm.1, hpow, mul_inv_cancel₀ ht.ne']
    constructor <;> norm_num
  have : g = (g * (h ^ n)⁻¹) * h ^ n := by simp
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure hgU)
    (Subgroup.pow_mem _ (Subgroup.subset_closure hhU) n)

end modulated

/-! ### The quotient by `k` -/

section quot

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (k : Subgroup G)

lemma top_cg_quot (h : IsCompactlyGeneratedSubgroup (⊤ : Subgroup G)) :
    IsCompactlyGeneratedSubgroup (⊤ : Subgroup (G ⧸ k)) := by
  obtain ⟨U, hU, -, ⟨V, hV, hVU⟩, hcl⟩ := h
  refine ⟨(QuotientGroup.mk : G → G ⧸ k) '' U, hU.image QuotientGroup.continuous_mk,
    fun _ _ => Subgroup.mem_top _, ⟨(QuotientGroup.mk : G → G ⧸ k) '' V, ?_, ?_⟩, ?_⟩
  · have := (QuotientGroup.isOpenMap_coe (N := k)).image_mem_nhds hV
    simpa using this
  · rintro _ ⟨⟨v, hv, rfl⟩, -⟩
    exact ⟨v, hVU ⟨hv, Subgroup.mem_top _⟩, rfl⟩
  · have := MonoidHom.map_closure (QuotientGroup.mk' k) U
    rw [hcl] at this
    rw [← QuotientGroup.coe_mk', ← this]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective k)

variable {m n r s : ℕ} {d : Fin s → ℕ}
  (π : (⊤ : Subgroup G) →* Multiplicative (ElemGroup m n r s d))

/-- the presentation induced on the quotient -/
noncomputable def barHom (hker : ∀ x (_ : x ∈ k), π ⟨x, Subgroup.mem_top x⟩ = 1) :
    (⊤ : Subgroup (G ⧸ k)) →* Multiplicative (ElemGroup m n r s d) :=
  (QuotientGroup.lift k (π.comp (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm.toMonoidHom)
    (fun x hx => MonoidHom.mem_ker.2 (hker x hx))).comp (Subgroup.subtype ⊤)

lemma barHom_mk (hker : ∀ x (_ : x ∈ k), π ⟨x, Subgroup.mem_top x⟩ = 1) (x : G)
    (hx : (x : G ⧸ k) ∈ (⊤ : Subgroup (G ⧸ k))) :
    barHom k π hker ⟨(x : G ⧸ k), hx⟩ = π ⟨x, Subgroup.mem_top x⟩ := rfl

lemma barHom_apply (hker : ∀ x (_ : x ∈ k), π ⟨x, Subgroup.mem_top x⟩ = 1) (y : G ⧸ k)
    (hy : y ∈ (⊤ : Subgroup (G ⧸ k))) (x : G) (hxy : (x : G ⧸ k) = y) :
    barHom k π hker ⟨y, hy⟩ = π ⟨x, Subgroup.mem_top x⟩ := by
  subst hxy; rfl

lemma barHom_pres (hπ : IsElemPresentation ⊤ k π)
    (hker : ∀ x (_ : x ∈ k), π ⟨x, Subgroup.mem_top x⟩ = 1) :
    IsElemPresentation (⊤ : Subgroup (G ⧸ k)) ⊥ (barHom k π hker) := by
  refine ⟨hπ.1, ?_, ?_, ?_, ?_⟩
  · have hl : Continuous (QuotientGroup.lift k (π.comp (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm.toMonoidHom)
        (fun x hx => MonoidHom.mem_ker.2 (hker x hx))) := by
      rw [(QuotientGroup.isQuotientMap_mk k).continuous_iff]
      exact hπ.2.1.comp (continuous_id.subtype_mk _)
    exact hl.comp continuous_subtype_val
  · intro V hV
    let q : (⊤ : Subgroup G) → (⊤ : Subgroup (G ⧸ k)) :=
      fun x => ⟨(x.1 : G ⧸ k), Subgroup.mem_top _⟩
    have hq : Continuous q := (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _
    have : barHom k π hker '' V = π '' (q ⁻¹' V) := by
      ext e
      constructor
      · rintro ⟨⟨y, hy⟩, hyV, rfl⟩
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
        exact ⟨⟨x, Subgroup.mem_top x⟩, hyV, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨q x, hx, rfl⟩
    rw [this]
    exact hπ.2.2.1 _ (hV.preimage hq)
  · intro e
    obtain ⟨x, rfl⟩ := hπ.2.2.2.1 e
    exact ⟨⟨(x.1 : G ⧸ k), Subgroup.mem_top _⟩, rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [barHom_mk, Subgroup.mem_bot]
    show _ ↔ (x : G ⧸ k) = 1
    rw [QuotientGroup.eq_one_iff]
    exact hπ.2.2.2.2 ⟨x, Subgroup.mem_top x⟩

lemma bot_structural [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [IsClosed (k : Set G)] (hcg : IsCompactlyGeneratedSubgroup (⊤ : Subgroup G))
    (hπ : IsElemPresentation ⊤ k π)
    (hker : ∀ x (_ : x ∈ k), π ⟨x, Subgroup.mem_top x⟩ = 1) :
    IsStructuralPair (⊤ : Subgroup (G ⧸ k)) ⊥ := by
  refine ⟨isOpen_univ, top_cg_quot k hcg, ⟨?_, ?_, ?_⟩, bot_le⟩
  · rw [Subgroup.coe_bot]; exact isClosed_singleton
  · have : annihilator (⊥ : Subgroup (G ⧸ k)) = Set.univ := by
      ext χ
      simp only [annihilator, Set.mem_univ, iff_true]
      intro x hx
      rw [Subgroup.mem_bot.1 hx, map_one]
    rw [this]; exact isOpen_univ
  · exact annihilator_isCompactlyGenerated (G ⧸ k) ⊥ ⊤
      (by rw [Subgroup.coe_bot]; exact isCompact_singleton) isOpen_univ bot_le
      (barHom k π hker) (barHom_pres k π hπ hker)

end quot

/-! ### The operators `W a` -/

section core

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {m' n' r' s' : ℕ} {d' : Fin s' → ℕ}
  (π : ↥(⊤ : Subgroup G) →* Multiplicative (ElemGroup m' n' r' s' d'))

/-- pull-back along `π`, as a linear map -/
noncomputable def pb : ElemSchwartz m' n' r' s' d' →ₗ[ℂ] (G → ℂ) where
  toFun g := fun x => g.toFun (Multiplicative.toAdd (π ⟨x, Subgroup.mem_top x⟩))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma pb_eq (g : ElemSchwartz m' n' r' s' d') : pb π g = extendPullback ⊤ π g.toFun := by
  funext x
  show g.toFun _ = extendPullback ⊤ π g.toFun x
  unfold extendPullback
  rw [dif_pos (Subgroup.mem_top x)]

lemma pb_injective (hsurj : Function.Surjective π) : Function.Injective (pb π) := by
  intro g g' h
  apply Subtype.ext
  funext e
  obtain ⟨x, hx⟩ := hsurj (Multiplicative.ofAdd e)
  have : g.toFun (Multiplicative.toAdd (π ⟨x.1, Subgroup.mem_top _⟩)) =
      g'.toFun (Multiplicative.toAdd (π ⟨x.1, Subgroup.mem_top _⟩)) := congrFun h (x : G)
  rw [Subtype.coe_eta, hx, toAdd_ofAdd] at this
  exact this

/-- multiplication by `m ^ a` on the stage -/
noncomputable def wt (m : G → ℝ) (I : Set ℝ) (k : Subgroup G) (a : ℝ) :
    ExpDecayStage G m I k →ₗ[ℂ] (G → ℂ) where
  toFun ϕ := fun x => ((m x ^ a : ℝ) : ℂ) * (ExpDecayStage.incl G m I k ϕ).toFun x
  map_add' ϕ ψ := by
    funext x
    show _ * ((ExpDecayStage.incl G m I k ϕ).toFun x + (ExpDecayStage.incl G m I k ψ).toFun x) = _
    simp only [Pi.add_apply]; ring
  map_smul' c ϕ := by
    funext x
    show _ * (c * (ExpDecayStage.incl G m I k ϕ).toFun x) = c * _
    ring

variable {m : G → ℝ} {I : Set ℝ} {k : Subgroup G}

open Classical in
/-- the operators `W a` -/
noncomputable def W (hinj : Function.Injective (pb π))
    (hr : ∀ a ∈ I, ∀ ϕ : ExpDecayStage G m I k, wt m I k a ϕ ∈ LinearMap.range (pb π))
    (a : ℝ) : ExpDecayStage G m I k →ₗ[ℂ] ElemSchwartz m' n' r' s' d' :=
  if h : a ∈ I then
    (LinearEquiv.ofInjective (pb π) hinj).symm.toLinearMap ∘ₗ
      (LinearMap.codRestrict _ (wt m I k a) (hr a h))
  else 0

lemma pb_W (hinj : Function.Injective (pb π))
    (hr : ∀ a ∈ I, ∀ ϕ : ExpDecayStage G m I k, wt m I k a ϕ ∈ LinearMap.range (pb π))
    {a : ℝ} (ha : a ∈ I) (ϕ : ExpDecayStage G m I k) :
    pb π (W π hinj hr a ϕ) = wt m I k a ϕ := by
  have := congrArg Subtype.val ((LinearEquiv.ofInjective (pb π) hinj).apply_symm_apply
    ⟨_, hr a ha ϕ⟩)
  rw [W, dif_pos ha]
  exact this

lemma expDecay_weighted_mem (m : G → ℝ) (I : Set ℝ) (f : G → ℂ)
    (hf : f ∈ expDecaySubmodule G m I) (a : ℝ) (ha : a ∈ I) :
    (fun g => ((m g ^ a : ℝ) : ℂ) * f g) ∈ schwartzBruhatSubmodule G := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hx.2 a ha
  | zero =>
    simp only [Pi.zero_apply, mul_zero]
    exact zero_mem _
  | add x y _ _ ihx ihy =>
    have := add_mem ihx ihy
    convert this using 1
    funext g
    simp [mul_add]
  | smul c x _ ih =>
    have := Submodule.smul_mem _ c ih
    convert this using 1
    funext g
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem core [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G → ℝ) (hm : IsRposModule m) (I : Set ℝ) (k : Subgroup G) (hk : IsGoodSubgroup k)
    (hπ : IsElemPresentation ⊤ k π) :
    ∃ (W : ℝ → ExpDecayStage G m I k →ₗ[ℂ] ElemSchwartz m' n' r' s' d')
      (Φ : ElemSchwartz m' n' r' s' d' ≃L[ℂ] SchwartzBruhat (G ⧸ k)),
      (∀ a ∈ I, ∀ (ϕ : ExpDecayStage G m I k) (x : G),
        (W a ϕ).toFun (Multiplicative.toAdd (π ⟨x, Subgroup.mem_top x⟩)) =
          ((m x ^ a : ℝ) : ℂ) * (ExpDecayStage.incl G m I k ϕ).toFun x) ∧
      (∀ a ∈ I, ∀ ϕ : ExpDecayStage G m I k, ExpDecaySchwartz.weighted k a ϕ.1 = Φ (W a ϕ)) ∧
      ∀ g : ℝ → ElemSchwartz m' n' r' s' d',
        (∀ a ∈ I, ∀ b ∈ I, ∀ x : G,
          (g a).toFun (Multiplicative.toAdd (π ⟨x, Subgroup.mem_top x⟩)) =
            ((m x ^ (a - b) : ℝ) : ℂ) *
              (g b).toFun (Multiplicative.toAdd (π ⟨x, Subgroup.mem_top x⟩))) →
        ∃ ϕ : ExpDecayStage G m I k, ∀ a ∈ I, W a ϕ = g a := by
  classical
  haveI : IsClosed (k : Set G) := hk.1
  have hkc := isCompact_of_isGoodSubgroup G k hk
  have hmk : ∀ h ∈ k, m h = 1 := fun h hh =>
    (isCompact_moduleKernel_and_compact_le G m hm (modKer hm.1) (fun g => Iff.rfl)).2 k hkc hh
  have hs : IsStructuralPair ⊤ k := ⟨isOpen_univ, top_cg hm, hk, le_top⟩
  have hinj : Function.Injective (pb π) := pb_injective π hπ.2.2.2.1
  have hker : ∀ x (_ : x ∈ k), π ⟨x, Subgroup.mem_top x⟩ = 1 :=
    fun x hx => (hπ.2.2.2.2 ⟨x, Subgroup.mem_top x⟩).2 hx
  have hr : ∀ a ∈ I, ∀ ϕ : ExpDecayStage G m I k, wt m I k a ϕ ∈ LinearMap.range (pb π) := by
    intro a ha ϕ
    obtain ⟨g, hg⟩ := descent k π hs hπ _ (expDecay_weighted_mem m I ϕ.1.1 ϕ.1.2 a ha)
      (fun x y hy => by
        show _ * ϕ.1.1 (x * y) = _ * ϕ.1.1 x
        rw [hm.1.map_mul, hmk y hy, mul_one, show ϕ.1.1 (x * y) = ϕ.1.1 x from ϕ.2 y hy x])
    exact ⟨g, by rw [pb_eq]; exact hg.symm⟩
  obtain ⟨Φ, hΦ⟩ := equiv_min (H := G ⧸ k) ⊥ m' n' r' s' d' (barHom k π hker)
    (bot_structural k π hs.2.1 hπ hker) (barHom_pres k π hπ hker) (fun _ _ => bot_le)
  refine ⟨W π hinj hr, Φ, ?_, ?_, ?_⟩
  · intro a ha ϕ x
    exact congrFun (pb_W π hinj hr ha ϕ) x
  · intro a ha ϕ
    have hfun : (fun x : G ⧸ k => ((m x.out ^ a : ℝ) : ℂ) * ϕ.1.toFun x.out) =
        (Φ (W π hinj hr a ϕ)).1 := by
      rw [hΦ]
      funext x
      show _ = extendPullback ⊤ (barHom k π hker) (W π hinj hr a ϕ).toFun x
      unfold extendPullback
      rw [dif_pos (Subgroup.mem_top x),
        barHom_apply k π hker x _ x.out (QuotientGroup.out_eq' x)]
      exact (congrFun (pb_W π hinj hr ha ϕ) x.out).symm
    have hmem : (fun x : G ⧸ k => ((m x.out ^ a : ℝ) : ℂ) * ϕ.1.toFun x.out) ∈
        schwartzBruhatSubmodule (G ⧸ k) := by
      rw [hfun]; exact (Φ (W π hinj hr a ϕ)).2
    unfold ExpDecaySchwartz.weighted
    exact (dif_pos hmem).trans (Subtype.ext hfun)
  · intro g hg
    by_cases hI : ∃ a₀, a₀ ∈ I
    · obtain ⟨a₀, ha₀⟩ := hI
      set f : G → ℂ := fun x => ((m x ^ (-a₀) : ℝ) : ℂ) *
        (g a₀).toFun (Multiplicative.toAdd (π ⟨x, Subgroup.mem_top x⟩)) with hfdef
      have hfw : ∀ a ∈ I, (fun x => ((m x ^ a : ℝ) : ℂ) * f x) = pb π (g a) := by
        intro a ha
        funext x
        show ((m x ^ a : ℝ) : ℂ) * (((m x ^ (-a₀) : ℝ) : ℂ) *
          (g a₀).toFun (Multiplicative.toAdd (π ⟨x, Subgroup.mem_top x⟩))) =
          (g a).toFun (Multiplicative.toAdd (π ⟨x, Subgroup.mem_top x⟩))
        rw [hg a ha a₀ ha₀ x, ← mul_assoc, ← Complex.ofReal_mul,
          ← Real.rpow_add (hm.1.pos x), sub_eq_add_neg]
      have hfc : Continuous f :=
        (Complex.continuous_ofReal.comp
          (hm.1.continuous.rpow_const (fun x => Or.inl (hm.1.pos x).ne'))).mul
        ((continuous_elemSchwartz _).comp
          (continuous_toAdd.comp (hπ.2.1.comp (continuous_id.subtype_mk _))))
      have hmem : f ∈ expDecaySubmodule G m I :=
        Submodule.subset_span ⟨hfc, fun a ha => by
          rw [hfw a ha, pb_eq]
          exact Submodule.subset_span ⟨⊤, k, _, _, _, _, _, π, g a, hs, hπ, rfl⟩⟩
      have hinv : ∀ h ∈ k, ∀ x : G, f (x * h) = f x := by
        intro h hh x
        have e : (⟨x * h, Subgroup.mem_top _⟩ : (⊤ : Subgroup G)) =
          ⟨x, Subgroup.mem_top x⟩ * ⟨h, Subgroup.mem_top h⟩ := rfl
        simp only [hfdef, hm.1.map_mul, hmk h hh, mul_one, e, map_mul, hker h hh]
      let ϕ₀ : ExpDecaySchwartz G m I := ⟨f, hmem⟩
      let ϕ : ExpDecayStage G m I k := ⟨ϕ₀, hinv⟩
      refine ⟨ϕ, fun a ha => ?_⟩
      apply hinj
      rw [pb_W π hinj hr ha ϕ]
      exact hfw a ha
    · exact ⟨0, fun a ha => absurd ⟨a, ha⟩ hI⟩

lemma topo_eq (m : G → ℝ) (I : Set ℝ) (k : Subgroup G)
    (W : ℝ → ExpDecayStage G m I k →ₗ[ℂ] ElemSchwartz m' n' r' s' d')
    (Φ : ElemSchwartz m' n' r' s' d' ≃L[ℂ] SchwartzBruhat (G ⧸ k))
    (h : ∀ a ∈ I, ∀ ϕ : ExpDecayStage G m I k, ExpDecaySchwartz.weighted k a ϕ.1 = Φ (W a ϕ)) :
    (inferInstance : TopologicalSpace (ExpDecayStage G m I k)) =
      ⨅ (a : ℝ) (_ : a ∈ I), TopologicalSpace.induced (W a) inferInstance := by
  show (⨅ (a : ℝ) (_ : a ∈ I), TopologicalSpace.induced
    (fun ϕ : ExpDecayStage G m I k => ExpDecaySchwartz.weighted k a ϕ.1) inferInstance) = _
  refine iInf_congr fun a => iInf_congr fun ha => ?_
  have h1 : (fun ϕ : ExpDecayStage G m I k => ExpDecaySchwartz.weighted k a ϕ.1) =
      Φ.toHomeomorph ∘ W a := funext (h a ha)
  rw [h1, ← induced_compose, Φ.toHomeomorph.induced_eq]

end core

end MasulloGRHStageConcreteAux

open MasulloGRH MasulloGRHStageConcreteAux in
theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hne : I.Nonempty) (k : Subgroup G) (hk : IsGoodSubgroup k) :
    IsStructuralPair ⊤ k ∧ IsNuclear (ExpDecayStage G m I k) ∧
    ∀ (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
      (π : ↥(⊤ : Subgroup G) →* Multiplicative (ElemGroup m' n' r' s' d')),
      IsElemPresentation ⊤ k π →
      ∃ W : ℝ → ExpDecayStage G m I k →ₗ[ℂ] ElemSchwartz m' n' r' s' d',
        (∀ a ∈ I, ∀ (ϕ : ExpDecayStage G m I k) (x : G),
          (W a ϕ).toFun (Multiplicative.toAdd (π ⟨x, Subgroup.mem_top x⟩)) =
            ((m x ^ a : ℝ) : ℂ) * (ExpDecayStage.incl G m I k ϕ).toFun x) ∧
        (inferInstance : TopologicalSpace (ExpDecayStage G m I k)) =
          ⨅ (a : ℝ) (_ : a ∈ I), TopologicalSpace.induced (W a) inferInstance ∧
        ∀ g : ℝ → ElemSchwartz m' n' r' s' d',
          (∀ a ∈ I, ∀ b ∈ I, ∀ x : G,
            (g a).toFun (Multiplicative.toAdd (π ⟨x, Subgroup.mem_top x⟩)) =
              ((m x ^ (a - b) : ℝ) : ℂ) *
                (g b).toFun (Multiplicative.toAdd (π ⟨x, Subgroup.mem_top x⟩))) →
          ∃ ϕ : ExpDecayStage G m I k, ∀ a ∈ I, W a ϕ = g a := by
  have hs : IsStructuralPair ⊤ k := ⟨isOpen_univ, top_cg hm, hk, le_top⟩
  haveI : IsClosed (k : Set G) := hk.1
  refine ⟨hs, ?_, ?_⟩
  · obtain ⟨m', n', r', s', d', π, hπ⟩ := exists_elemPresentation_of_isStructuralPair G ⊤ k hs
    obtain ⟨W, Φ, hWa, hWb, -⟩ := core π m hm I k hk hπ
    have hN : IsNuclear (SchwartzBruhat (G ⧸ k)) :=
      (schwartzBruhat_main_structure (G ⧸ k)).2.2.2.2.1
    refine nuclear_of_projective_topology (ULift.{u} {a : ℝ // a ∈ I})
      (fun _ => SchwartzBruhat (G ⧸ k)) (fun _ => hN) (ExpDecayStage G m I k)
      (fun i => Φ.toLinearEquiv.toLinearMap ∘ₗ W i.down.1) ?_ ?_
    · show (⨅ (a : ℝ) (_ : a ∈ I), TopologicalSpace.induced
        (fun ϕ : ExpDecayStage G m I k => ExpDecaySchwartz.weighted k a ϕ.1) inferInstance) = _
      apply le_antisymm
      · refine le_iInf fun i => iInf₂_le_of_le i.down.1 i.down.2 (le_of_eq ?_)
        exact congrArg (fun f => TopologicalSpace.induced f _) (funext (hWb _ i.down.2))
      · refine le_iInf₂ fun a ha => iInf_le_of_le ⟨⟨a, ha⟩⟩ (le_of_eq ?_)
        exact congrArg (fun f => TopologicalSpace.induced f _) (funext (hWb a ha)).symm
    · intro ϕ h0
      obtain ⟨a, ha⟩ := hne
      have h1 : W a ϕ = 0 := Φ.map_eq_zero_iff.1 (h0 ⟨⟨a, ha⟩⟩)
      apply Subtype.ext
      apply Subtype.ext
      funext x
      have h2 := hWa a ha ϕ x
      rw [h1] at h2
      have hpos : ((m x ^ a : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.rpow_pos_of_pos (hm.1.pos x) a).ne'
      exact (mul_eq_zero.1 h2.symm).resolve_left hpos
  · intro m' n' r' s' d' π hπ
    obtain ⟨W, Φ, hWa, hWb, hWc⟩ := core π m hm I k hk hπ
    exact ⟨W, hWa, topo_eq m I k W Φ hWb, hWc⟩
