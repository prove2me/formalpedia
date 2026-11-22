-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_fourier_oneParameterDeriv
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:21:19.553586+00:00
-- url     : https://prove2.me/submissions/a4bc2286-98a9-4153-86f2-ae7df38de4f9

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
import Theorems.Thm_MasulloGRH_schwartzBruhat_oneParameterDeriv
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Theorems.Thm_MasulloGRH_isRapidDecay_elemSchwartz_toFun

open MeasureTheory Topology Filter

set_option autoImplicit false

namespace Sol_MasulloGRH_schwartzBruhat_fourier_oneParameterDeriv

open MasulloGRH
open scoped Pointwise

/-! ### Continuity of Schwartz–Bruhat functions -/

theorem continuous_elem {m n r s : ℕ} {d : Fin s → ℕ} (g : ElemSchwartz m n r s d) :
    Continuous g.toFun := by
  have hg := (isRapidDecay_elemSchwartz_toFun g).1
  let q : (Fin m → ℝ) × (Fin n → ℝ) × (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) →
      ElemGroup m n r s d :=
    Prod.map id (Prod.map (Pi.map fun _ => (QuotientAddGroup.mk : ℝ → UnitAddCircle)) id)
  have hq : IsQuotientMap q :=
    (IsOpenQuotientMap.id.prodMap
      ((IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk).prodMap
        IsOpenQuotientMap.id)).isQuotientMap
  rw [hq.continuous_iff, continuous_iff_continuousAt]
  rintro ⟨x₀, t₀, a₀, b₀⟩
  have hcont : Continuous (fun p : (Fin m → ℝ) × (Fin n → ℝ) × (Fin r → ℤ) ×
      ((i : Fin s) → ZMod (d i)) => elemLift g.toFun a₀ b₀ (p.1, p.2.1)) :=
    (hg a₀ b₀).continuous.comp (by fun_prop)
  refine hcont.continuousAt.congr ?_
  have hopen : IsOpen {p : (Fin m → ℝ) × (Fin n → ℝ) × (Fin r → ℤ) ×
      ((i : Fin s) → ZMod (d i)) | p.2.2 = (a₀, b₀)} :=
    (isOpen_discrete {((a₀, b₀) : (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)))}).preimage
      (by fun_prop)
  filter_upwards [hopen.mem_nhds rfl] with p hp
  obtain ⟨x, t, a, b⟩ := p
  simp only [Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  rfl

theorem continuous_extendPullback {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] {m n r s : ℕ} {d : Fin s → ℕ} (Γ : Subgroup G)
    (hΓ : IsOpen (Γ : Set G)) (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hπ : Continuous π) (g : ElemGroup m n r s d → ℂ) (hg : Continuous g) :
    Continuous (extendPullback Γ π g) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Γ
  · have hon : ContinuousOn (extendPullback Γ π g) (Γ : Set G) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : Set.domRestrict (Γ : Set G) (extendPullback Γ π g) =
          fun y : (Γ : Set G) => g (Multiplicative.toAdd (π ⟨y.1, y.2⟩)) := by
        funext y
        show extendPullback Γ π g y.1 = _
        exact dif_pos y.2
      rw [this]
      exact hg.comp (continuous_toAdd.comp (hπ.comp (by fun_prop)))
    exact hon.continuousAt (hΓ.mem_nhds hx)
  · have hcl : IsClosed (Γ : Set G) := Subgroup.isClosed_of_isOpen Γ hΓ
    have h0 : extendPullback Γ π g =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
      simp only [extendPullback, dif_neg (show y ∉ Γ from hy)]
    exact continuousAt_const.congr h0.symm

theorem continuous_sb {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : SchwartzBruhat G) : Continuous (f : G → ℂ) := by
  obtain ⟨f, hf⟩ := f
  show Continuous f
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hx
    exact continuous_extendPullback Γ hs.1 π hπ.2.1 _ (continuous_elem g)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

/-! ### Integrability of Schwartz–Bruhat functions -/

/-! ### A reference Haar measure on `ℝ^m × 𝕋^n × ℤ^r × F` -/

instance bs3 {n r s : ℕ} {d : Fin s → ℕ} [∀ i, NeZero (d i)] :
    BorelSpace ((Fin n → UnitAddCircle) × (Fin r → ℤ) × ((i : Fin s) → ZMod (d i))) :=
  Prod.borelSpace

instance bsE {m n r s : ℕ} {d : Fin s → ℕ} [∀ i, NeZero (d i)] : BorelSpace (ElemGroup m n r s d) :=
  Prod.borelSpace

instance countHaar {A : Type*} [AddGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableAdd A] :
    (Measure.count : Measure A).IsAddHaarMeasure where
  lt_top_of_isCompact := fun K hK => (Measure.count_apply_lt_top).2 hK.finite_of_discrete
  open_pos := fun U _ hne => by
    rw [Ne, Measure.count_eq_zero_iff]; exact hne.ne_empty
  map_add_left_eq_self :=
    (inferInstance : (Measure.count : Measure A).IsAddLeftInvariant).map_add_left_eq_self

/-- The product Haar measure on `ℝ^m × 𝕋^n × ℤ^r × F`. -/
noncomputable def lam (m n r s : ℕ) (d : Fin s → ℕ) : Measure (ElemGroup m n r s d) :=
  (Measure.pi fun _ => volume).prod ((Measure.pi fun _ => volume).prod
    ((Measure.pi fun _ => Measure.count).prod (Measure.pi fun _ => Measure.count)))

instance lam_haar {m n r s : ℕ} {d : Fin s → ℕ} [∀ i, NeZero (d i)] :
    (lam m n r s d).IsAddHaarMeasure := by
  unfold lam
  have h4 : ((Measure.pi fun _ => Measure.count).prod (Measure.pi fun i => Measure.count) :
      Measure ((Fin r → ℤ) × ((i : Fin s) → ZMod (d i)))).IsAddHaarMeasure := inferInstance
  have h3 : ((Measure.pi fun _ => volume).prod
      ((Measure.pi fun _ => Measure.count).prod (Measure.pi fun i => Measure.count)) :
      Measure ((Fin n → UnitAddCircle) × (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  exact Measure.prod.instIsAddHaarMeasure _ _

/-! ### Decay weights -/

/-- The weight `(1 + ‖t‖)⁻²`. -/
noncomputable def w {α : Type*} [Norm α] (t : α) : ℝ := ((1 + ‖t‖) ^ 2)⁻¹

theorem w_nonneg {α : Type*} [Norm α] [Nonempty α] (t : α) (ht : 0 ≤ ‖t‖) : 0 ≤ w t := by
  unfold w; positivity

theorem integrable_w_real : Integrable (fun t : ℝ => w t) volume := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  refine h.congr (ae_of_all _ fun t => ?_)
  simp only [w]
  rw [Real.rpow_neg (by positivity), Real.rpow_two]

theorem integrable_w_int : Integrable (fun a : ℤ => w a) Measure.count := by
  rw [integrable_count_iff]
  have hs := (Real.summable_one_div_int_add_rpow (1 / 2) 2).2 (by norm_num)
  refine Summable.of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_) hs
  have hpos : (1 / 2 : ℝ) ≤ |(a : ℝ) + 1 / 2| := by
    rcases le_or_gt 0 a with h | h
    · have : (0 : ℝ) ≤ a := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
    · have : (a : ℝ) ≤ -1 := by exact_mod_cast (show a ≤ -1 by omega)
      rw [abs_of_neg (by linarith)]; linarith
  have hle : |(a : ℝ) + 1 / 2| ≤ 1 + ‖a‖ := by
    rw [Int.norm_eq_abs]
    calc |(a : ℝ) + 1 / 2| ≤ |(a : ℝ)| + |1 / 2| := abs_add_le _ _
      _ ≤ 1 + |(a : ℝ)| := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith
  rw [Real.norm_of_nonneg (by unfold w; positivity), Real.rpow_two]
  unfold w
  rw [one_div]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hle 2)

theorem integrable_weight (m n r s : ℕ) (d : Fin s → ℕ) [∀ i, NeZero (d i)] :
    Integrable (fun y : ElemGroup m n r s d =>
      (∏ i, w (y.1 i)) * (1 * ((∏ j, w (y.2.2.1 j)) * 1))) (lam m n r s d) := by
  have h1 : Integrable (fun x : Fin m → ℝ => ∏ i, w (x i)) (Measure.pi fun _ => volume) :=
    Integrable.fintype_prod (f := fun _ t => w t) (fun _ => integrable_w_real)
  have h3 : Integrable (fun a : Fin r → ℤ => ∏ j, w (a j)) (Measure.pi fun _ => Measure.count) :=
    Integrable.fintype_prod (f := fun _ t => w t) (fun _ => integrable_w_int)
  exact h1.mul_prod ((integrable_const (1 : ℝ)).mul_prod (h3.mul_prod (integrable_const (1 : ℝ))))

theorem one_add_pow_le (u : ℝ) (hu : 0 ≤ u) (N : ℕ) : (1 + u) ^ N ≤ 2 ^ N * (1 + u ^ N) := by
  rcases le_total u 1 with h | h
  · calc (1 + u) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ ≤ 2 ^ N * (1 + u ^ N) :=
          le_mul_of_one_le_right (by positivity) (by have := pow_nonneg hu N; linarith)
  · calc (1 + u) ^ N ≤ (2 * u) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ = 2 ^ N * u ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + u ^ N) := by gcongr; linarith

theorem prod_w_ge {α : Type*} [SeminormedAddCommGroup α] {k : ℕ} (x : Fin k → α) :
    ((1 + ‖x‖) ^ (2 * k))⁻¹ ≤ ∏ i, w (x i) := by
  simp only [w]
  rw [Finset.prod_inv_distrib]
  refine inv_anti₀ (Finset.prod_pos fun i _ => by positivity) ?_
  calc ∏ i, (1 + ‖x i‖) ^ 2 ≤ ∏ _i : Fin k, (1 + ‖x‖) ^ 2 :=
        Finset.prod_le_prod (fun i _ => by positivity)
          (fun i _ => pow_le_pow_left₀ (by positivity) (by linarith [norm_le_pi_norm x i]) 2)
    _ = (1 + ‖x‖) ^ (2 * k) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

theorem decay {m n r s : ℕ} {d : Fin s → ℕ} (g : ElemGroup m n r s d → ℂ) (hg : IsRapidDecay g) :
    ∃ K : ℝ, ∀ y : ElemGroup m n r s d,
      ‖g y‖ ≤ K * ((∏ i, w (y.1 i)) * (1 * ((∏ j, w (y.2.2.1 j)) * 1))) := by
  obtain ⟨C00, h00⟩ := hg.2 0 0 0
  obtain ⟨C10, h10⟩ := hg.2 (2 * m) 0 0
  obtain ⟨C01, h01⟩ := hg.2 0 (2 * r) 0
  obtain ⟨C11, h11⟩ := hg.2 (2 * m) (2 * r) 0
  refine ⟨2 ^ (2 * m) * 2 ^ (2 * r) * (C00 + C10 + C01 + C11), ?_⟩
  rintro ⟨x, z, a, b⟩
  have hz : ∃ t : Fin n → ℝ, (fun j => ((t j : ℝ) : UnitAddCircle)) = z :=
    ⟨fun j => (QuotientAddGroup.mk_surjective (z j)).choose,
      funext fun j => (QuotientAddGroup.mk_surjective (z j)).choose_spec⟩
  obtain ⟨t, rfl⟩ := hz
  have key : ∀ i j : ℕ, ∀ C : ℝ, (∀ a b xt, ‖a‖ ^ j * ‖xt.1‖ ^ i *
      ‖iteratedFDeriv ℝ 0 (elemLift g a b) xt‖ ≤ C) →
      ‖a‖ ^ j * ‖x‖ ^ i * ‖g (x, fun j => ((t j : ℝ) : UnitAddCircle), a, b)‖ ≤ C := by
    intro i j C h
    have := h a b (x, t)
    rwa [norm_iteratedFDeriv_zero] at this
  have e00 := key 0 0 C00 h00
  have e10 := key (2 * m) 0 C10 h10
  have e01 := key 0 (2 * r) C01 h01
  have e11 := key (2 * m) (2 * r) C11 h11
  simp only [pow_zero, one_mul] at e00 e10 e01
  set G := ‖g (x, fun j => ((t j : ℝ) : UnitAddCircle), a, b)‖ with hG
  set X := ‖x‖
  set A := ‖a‖
  have hX : 0 ≤ X := norm_nonneg _
  have hA : 0 ≤ A := norm_nonneg _
  have hG0 : 0 ≤ G := norm_nonneg _
  have hp1 := prod_w_ge x
  have hp3 := prod_w_ge a
  simp only [mul_one, one_mul]
  have hXN := one_add_pow_le X hX (2 * m)
  have hAM := one_add_pow_le A hA (2 * r)
  have hq1 : 0 < (1 + X) ^ (2 * m) := by positivity
  have hq3 : 0 < (1 + A) ^ (2 * r) := by positivity
  -- G (1+X)^N (1+A)^M ≤ K
  have hmain : G * ((1 + X) ^ (2 * m) * (1 + A) ^ (2 * r)) ≤
      2 ^ (2 * m) * 2 ^ (2 * r) * (C00 + C10 + C01 + C11) := by
    calc G * ((1 + X) ^ (2 * m) * (1 + A) ^ (2 * r))
        ≤ G * ((2 ^ (2 * m) * (1 + X ^ (2 * m))) * (2 ^ (2 * r) * (1 + A ^ (2 * r)))) := by
          gcongr
      _ = 2 ^ (2 * m) * 2 ^ (2 * r) * (G + X ^ (2 * m) * G + A ^ (2 * r) * G +
            A ^ (2 * r) * X ^ (2 * m) * G) := by ring
      _ ≤ 2 ^ (2 * m) * 2 ^ (2 * r) * (C00 + C10 + C01 + C11) := by
          gcongr
          linarith
  have hK0 : 0 ≤ 2 ^ (2 * m) * 2 ^ (2 * r) * (C00 + C10 + C01 + C11) :=
    le_trans (by positivity) hmain
  calc G = G * ((1 + X) ^ (2 * m) * (1 + A) ^ (2 * r)) *
        (((1 + X) ^ (2 * m))⁻¹ * ((1 + A) ^ (2 * r))⁻¹) := by
          field_simp
    _ ≤ 2 ^ (2 * m) * 2 ^ (2 * r) * (C00 + C10 + C01 + C11) *
        (((1 + X) ^ (2 * m))⁻¹ * ((1 + A) ^ (2 * r))⁻¹) := by
          gcongr
    _ ≤ 2 ^ (2 * m) * 2 ^ (2 * r) * (C00 + C10 + C01 + C11) *
        ((∏ i, w (x i)) * ∏ j, w (a j)) := by
          gcongr
          exact le_trans (by positivity) hp1

theorem integrable_elem {m n r s : ℕ} {d : Fin s → ℕ} [∀ i, NeZero (d i)]
    (g : ElemSchwartz m n r s d) (ρ : Measure (ElemGroup m n r s d)) [ρ.IsAddHaarMeasure] :
    Integrable g.toFun ρ := by
  obtain ⟨K, hK⟩ := decay g.toFun (isRapidDecay_elemSchwartz_toFun g)
  have hl : Integrable g.toFun (lam m n r s d) :=
    ((integrable_weight m n r s d).const_mul K).mono'
      (continuous_elem g).aestronglyMeasurable (ae_of_all _ hK)
  rw [Measure.isAddLeftInvariant_eq_smul ρ (lam m n r s d)]
  exact hl.smul_measure_nnreal

/-! ### Pulling back along a presentation -/

section group_int

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

theorem integrable_stage (μ : Measure G) [μ.IsHaarMeasure] (Γ k : Subgroup G) {m n r s : ℕ}
    {d : Fin s → ℕ} (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) (g : ElemSchwartz m n r s d) :
    Integrable (extendPullback Γ π g.toFun) μ := by
  have : ∀ i, NeZero (d i) := fun i => ⟨hπ.1 i⟩
  have hΓo : IsOpen (Γ : Set G) := hs.1
  have hΓc : IsClosed (Γ : Set G) := Subgroup.isClosed_of_isOpen Γ hΓo
  have : LocallyCompactSpace Γ := hΓc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hk : IsCompact (k : Set G) := isCompact_of_isGoodSubgroup G k hs.2.2.1
  -- the Haar measure of `Γ`
  have hν : (μ.comap (Γ.subtype : Γ → G)).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := ContinuousMul.measurableMul) μ (f := Γ.subtype)
      hΓo.isOpenEmbedding_subtypeVal
  -- `π` is proper
  have hprop : Tendsto π (cocompact Γ) (cocompact (Multiplicative (ElemGroup m n r s d))) := by
    refine (hasBasis_cocompact.tendsto_iff hasBasis_cocompact).2 fun B hB => ?_
    have hloc : ∀ y ∈ B, ∃ N : Set Γ, IsCompact N ∧ (π '' N) ∈ 𝓝 y := by
      intro y _
      obtain ⟨x, rfl⟩ := hπ.2.2.2.1 y
      obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x
      exact ⟨N, hNc, hπ.2.2.1.image_mem_nhds hN⟩
    choose! N hNc hN using hloc
    obtain ⟨t, htB, hcover⟩ := hB.elim_nhds_subcover (fun y => π '' N y) hN
    have hK : IsCompact (⋃ y ∈ t, N y) := t.isCompact_biUnion fun y hy => hNc y (htB y hy)
    have hker : IsCompact (Subtype.val ⁻¹' (k : Set G) : Set Γ) :=
      hΓc.isClosedEmbedding_subtypeVal.isCompact_preimage hk
    refine ⟨(⋃ y ∈ t, N y) * (Subtype.val ⁻¹' (k : Set G)), hK.mul hker, fun x hx hxB => hx ?_⟩
    obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.1 (hcover hxB)
    obtain ⟨x', hx'N, hx'⟩ := hy
    refine ⟨x', Set.mem_biUnion hyt hx'N, x'⁻¹ * x, ?_, mul_inv_cancel_left x' x⟩
    have h1 : π (x'⁻¹ * x) = 1 := by rw [map_mul, map_inv, hx', inv_mul_cancel]
    exact (hπ.2.2.2.2 _).1 h1
  -- the push-forward is a Haar measure on the elementary group
  letI : MeasurableSpace (Multiplicative (ElemGroup m n r s d)) :=
    (inferInstance : MeasurableSpace (ElemGroup m n r s d))
  have : BorelSpace (Multiplicative (ElemGroup m n r s d)) :=
    ⟨(BorelSpace.measurable_eq : (inferInstance : MeasurableSpace (ElemGroup m n r s d)) =
      borel (ElemGroup m n r s d))⟩
  have hρ : ((μ.comap (Γ.subtype : Γ → G)).map π).IsHaarMeasure :=
    Measure.isHaarMeasure_map _ π hπ.2.1 hπ.2.2.2.1 hprop
  let ρ : Measure (ElemGroup m n r s d) := (μ.comap (Γ.subtype : Γ → G)).map π
  have : ρ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hρ.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hρ.toIsOpenPosMeasure
      map_add_left_eq_self := fun x => hρ.map_mul_left_eq_self (Multiplicative.ofAdd x) }
  have hgρ : Integrable g.toFun ρ := integrable_elem g ρ
  have hcomp : Integrable (fun x : Γ => g.toFun (Multiplicative.toAdd (π x)))
      (μ.comap (Γ.subtype : Γ → G)) :=
    hgρ.comp_measurable hπ.2.1.measurable
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := (Γ : Set G))
  · rw [integrableOn_iff_comap_subtypeVal hΓo.measurableSet]
    refine hcomp.congr (ae_of_all _ fun x => ?_)
    show g.toFun (Multiplicative.toAdd (π x)) = extendPullback Γ π g.toFun x.1
    simp only [extendPullback, dif_pos x.2]
  · intro x hx
    simp only [extendPullback, dif_neg (show x ∉ Γ from hx)]

theorem integrable_sb' (μ : Measure G) [μ.IsHaarMeasure] (f : SchwartzBruhat G) :
    Integrable (f : G → ℂ) μ := by
  obtain ⟨f, hf⟩ := f
  show Integrable f μ
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hx
    exact integrable_stage μ Γ k π hs hπ g
  | zero => exact integrable_zero _ _ _
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.smul a

end group_int

/-! ### Supports in compactly generated subgroups and σ-finiteness -/

section support

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem support_closure (f : G → ℂ) (hf : f ∈ schwartzBruhatSubmodule G) :
    ∃ C : Set G, IsCompact C ∧ ∀ x, x ∉ Subgroup.closure C → f x = 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hx
    obtain ⟨U, hU, -, -, hUΓ⟩ := hs.2.1
    refine ⟨U, hU, fun x hx => ?_⟩
    rw [hUΓ] at hx
    simp only [extendPullback, dif_neg hx]
  | zero => exact ⟨∅, isCompact_empty, fun _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨C₁, hC₁, h₁⟩ := hx
    obtain ⟨C₂, hC₂, h₂⟩ := hy
    refine ⟨C₁ ∪ C₂, hC₁.union hC₂, fun z hz => ?_⟩
    have hz₁ : z ∉ Subgroup.closure C₁ := fun h =>
      hz (Subgroup.closure_mono Set.subset_union_left h)
    have hz₂ : z ∉ Subgroup.closure C₂ := fun h =>
      hz (Subgroup.closure_mono Set.subset_union_right h)
    simp [h₁ z hz₁, h₂ z hz₂]
  | smul c x _ hx =>
    obtain ⟨C, hC, h⟩ := hx
    exact ⟨C, hC, fun z hz => by simp [h z hz]⟩

theorem closure_subset_iUnion_pow (C : Set G) :
    (Subgroup.closure C : Set G) ⊆ ⋃ n : ℕ, (C ∪ C⁻¹ ∪ {1}) ^ n := by
  intro x hx
  have hSinv : (C ∪ C⁻¹ ∪ {1})⁻¹ = C ∪ C⁻¹ ∪ {1} := by
    simp only [Set.union_inv, inv_inv, Set.inv_singleton, inv_one]
    rw [Set.union_comm C⁻¹ C]
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact Set.mem_iUnion.2 ⟨1, by rw [pow_one]; exact Or.inl (Or.inl hy)⟩
  | one => exact Set.mem_iUnion.2 ⟨0, by rw [pow_zero]; exact Set.mem_one.2 rfl⟩
  | mul y z _ _ hy hz =>
    obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hy
    obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hz
    exact Set.mem_iUnion.2 ⟨p + q, by rw [pow_add]; exact Set.mul_mem_mul hp hq⟩
  | inv y _ hy =>
    obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hy
    refine Set.mem_iUnion.2 ⟨p, ?_⟩
    have : y⁻¹ ∈ ((C ∪ C⁻¹ ∪ {1}) ^ p)⁻¹ := Set.inv_mem_inv.2 hp
    rwa [← inv_pow, hSinv] at this

theorem isCompact_pow' {S : Set G} (hS : IsCompact S) (n : ℕ) : IsCompact (S ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact isCompact_singleton
  | succ n ih => rw [pow_succ]; exact ih.mul hS

variable [MeasurableSpace G] [BorelSpace G] [T2Space G]

theorem sigmaFinite_restrict (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (C : Set G) (hC : IsCompact C) (H : Set G) (hH : H ⊆ Subgroup.closure C) :
    SigmaFinite (μ.restrict H) := by
  have hSc : IsCompact (C ∪ C⁻¹ ∪ {1}) := (hC.union hC.inv).union isCompact_singleton
  have hTm : MeasurableSet (⋃ n : ℕ, (C ∪ C⁻¹ ∪ {1}) ^ n) :=
    MeasurableSet.iUnion fun n => (isCompact_pow' hSc n).isClosed.measurableSet
  have hT : SigmaFinite (μ.restrict (⋃ n : ℕ, (C ∪ C⁻¹ ∪ {1}) ^ n)) := by
    refine ⟨⟨{ set := (fun n => (C ∪ C⁻¹ ∪ {1}) ^ n ∪ (⋃ n : ℕ, (C ∪ C⁻¹ ∪ {1}) ^ n)ᶜ),
                set_mem := fun _ => trivial,
                finite := fun n => ?_,
                spanning := ?_ }⟩⟩
    · refine lt_of_le_of_lt (measure_union_le _ _) ?_
      rw [Measure.restrict_apply hTm.compl, Set.compl_inter_self, measure_empty, add_zero]
      exact lt_of_le_of_lt (Measure.restrict_apply_le _ _) (isCompact_pow' hSc n).measure_lt_top
    · ext x
      simp only [Set.mem_iUnion, Set.mem_union, Set.mem_univ, iff_true]
      by_cases hx : x ∈ ⋃ n : ℕ, (C ∪ C⁻¹ ∪ {1}) ^ n
      · obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
        exact ⟨n, Or.inl hn⟩
      · exact ⟨0, Or.inr hx⟩
  exact Measure.sigmaFinite_of_le _ (Measure.restrict_mono (hH.trans (closure_subset_iUnion_pow C)) le_rfl)

end support

/-! ### The Fourier computation -/

section fourier

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

theorem integrable_mul_char {f : G → ℂ} (hf : Integrable f μ) (χ : PontryaginDual G) :
    Integrable (fun x => f x * star ((χ x : ℂ))) μ := by
  refine Integrable.mono' hf.norm (hf.aestronglyMeasurable.mul ?_) (ae_of_all _ fun x => ?_)
  · exact (continuous_star.comp (continuous_subtype_val.comp χ.continuous)).aestronglyMeasurable
  · rw [norm_mul, norm_star, Circle.norm_coe, mul_one]

theorem fourier_translate (F : G → ℂ) (χ : PontryaginDual G) (y : G) :
    ∫ x, F (x * y) * star ((χ x : ℂ)) ∂μ = (χ y : ℂ) * ∫ x, F x * star ((χ x : ℂ)) ∂μ := by
  have h := integral_mul_right_eq_self (μ := μ) (fun x => F x * star ((χ (x * y⁻¹) : ℂ))) y
  simp only [mul_inv_cancel_right] at h
  rw [h, ← integral_const_mul]
  congr 1
  funext x
  rw [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv_eq_conj, star_mul', Complex.star_def,
    Complex.conj_conj]
  ring

theorem key (f h : G → ℂ) (hf : Integrable f μ) (hh : Integrable h μ) (hhc : Continuous h)
    (a : Multiplicative ℝ →ₜ* G)
    (hderiv : ∀ g, HasDerivAt (fun t : ℝ => f (g * a (Multiplicative.ofAdd t))) (h g) 0)
    (Γ₀ : Subgroup G) (hΓ₀ : IsOpen (Γ₀ : Set G)) [SigmaFinite (μ.restrict (Γ₀ : Set G))]
    (hhΓ : ∀ x ∉ Γ₀, h x = 0) (χ : PontryaginDual G) :
    RiemannMasullo.lcaFourier μ h χ =
      deriv (fun t : ℝ => ((χ (a (Multiplicative.ofAdd t)) : Circle) : ℂ)) 0 *
        RiemannMasullo.lcaFourier μ f χ := by
  set e : ℝ → ℂ := fun t => ((χ (a (Multiplicative.ofAdd t)) : Circle) : ℂ) with he_def
  have hac : Continuous (fun t : ℝ => a (Multiplicative.ofAdd t)) :=
    a.continuous.comp continuous_ofAdd
  have he : Continuous e := continuous_subtype_val.comp (χ.continuous.comp hac)
  have he0 : e 0 = 1 := by simp [e]
  have hadd : ∀ s t : ℝ, a (Multiplicative.ofAdd (s + t)) =
      a (Multiplicative.ofAdd s) * a (Multiplicative.ofAdd t) := fun s t => by
    rw [ofAdd_add, map_mul]
  -- the one-parameter subgroup lies in the open subgroup `Γ₀`
  have hmem : ∀ t : ℝ, a (Multiplicative.ofAdd t) ∈ Γ₀ := by
    have hcl : IsClopen ((fun t : ℝ => a (Multiplicative.ofAdd t)) ⁻¹' (Γ₀ : Set G)) :=
      ⟨(Subgroup.isClosed_of_isOpen Γ₀ hΓ₀).preimage hac, hΓ₀.preimage hac⟩
    have huniv := hcl.eq_univ ⟨0, by simp [Γ₀.one_mem]⟩
    intro t
    have : t ∈ (fun t : ℝ => a (Multiplicative.ofAdd t)) ⁻¹' (Γ₀ : Set G) := by
      rw [huniv]; trivial
    exact this
  -- fundamental theorem of calculus along the orbits
  have hftc : ∀ (x : G) (t : ℝ), ∫ s in (0 : ℝ)..t, h (x * a (Multiplicative.ofAdd s)) =
      f (x * a (Multiplicative.ofAdd t)) - f x := by
    intro x t
    have hd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => f (x * a (Multiplicative.ofAdd u)))
        (h (x * a (Multiplicative.ofAdd s))) s := by
      intro s
      have h1 := hderiv (x * a (Multiplicative.ofAdd s))
      have h2 : HasDerivAt (fun u : ℝ => f (x * a (Multiplicative.ofAdd s) *
          a (Multiplicative.ofAdd (u - s)))) (h (x * a (Multiplicative.ofAdd s))) s :=
        HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
      show f (x * a (Multiplicative.ofAdd u)) =
        f (x * a (Multiplicative.ofAdd s) * a (Multiplicative.ofAdd (u - s)))
      rw [mul_assoc, ← hadd, add_sub_cancel]
    have hcont : Continuous (fun s : ℝ => h (x * a (Multiplicative.ofAdd s))) :=
      hhc.comp (continuous_const.mul hac)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      (hcont.intervalIntegrable _ _)]
    simp
  -- vanishing outside `Γ₀`
  have hvan : ∀ (s : ℝ) (x : G), x ∉ Γ₀ → h (x * a (Multiplicative.ofAdd s)) = 0 := by
    intro s x hx
    exact hhΓ _ (fun h' => hx ((Subgroup.mul_mem_cancel_right Γ₀ (hmem s)).1 h'))
  have htr : ∀ (F : G → ℂ) (t : ℝ), ∫ x, F (x * a (Multiplicative.ofAdd t)) *
      star ((χ x : ℂ)) ∂μ = e t * ∫ x, F x * star ((χ x : ℂ)) ∂μ :=
    fun F t => fourier_translate μ F χ _
  -- the integrated identity
  have hid : ∀ t : ℝ, e t * RiemannMasullo.lcaFourier μ f χ - RiemannMasullo.lcaFourier μ f χ =
      RiemannMasullo.lcaFourier μ h χ * ∫ s in (0 : ℝ)..t, e s := by
    intro t
    have hfa : Integrable (fun x => f (x * a (Multiplicative.ofAdd t))) μ :=
      hf.comp_mul_right _
    have h1 : e t * RiemannMasullo.lcaFourier μ f χ - RiemannMasullo.lcaFourier μ f χ =
        ∫ x, (f (x * a (Multiplicative.ofAdd t)) - f x) * star ((χ x : ℂ)) ∂μ := by
      simp only [sub_mul]
      rw [integral_sub (integrable_mul_char μ hfa χ) (integrable_mul_char μ hf χ), htr f t]
      rfl
    rw [h1]
    simp_rw [← hftc, ← intervalIntegral.integral_mul_const]
    have hzero : ∀ x, x ∉ (Γ₀ : Set G) →
        (∫ s in (0 : ℝ)..t, h (x * a (Multiplicative.ofAdd s)) * star ((χ x : ℂ))) = 0 := by
      intro x hx
      simp [hvan _ x hx]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    -- Fubini on `[0, t] × Γ₀`
    have hint : Integrable (Function.uncurry fun (s : ℝ) (x : G) =>
        h (x * a (Multiplicative.ofAdd s)) * star ((χ x : ℂ)))
        ((volume.restrict (Set.uIoc 0 t)).prod (μ.restrict (Γ₀ : Set G))) := by
      have hcont2 : Continuous (Function.uncurry fun (s : ℝ) (x : G) =>
          h (x * a (Multiplicative.ofAdd s)) * star ((χ x : ℂ))) := by
        refine (hhc.comp (continuous_snd.mul (hac.comp continuous_fst))).mul ?_
        exact continuous_star.comp (continuous_subtype_val.comp (χ.continuous.comp continuous_snd))
      have : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
        refine ⟨?_⟩
        rw [Measure.restrict_apply_univ, Set.uIoc]
        exact measure_Ioc_lt_top
      rw [integrable_prod_iff hcont2.aestronglyMeasurable]
      refine ⟨ae_of_all _ fun s => ?_, ?_⟩
      · exact (integrable_mul_char μ (hh.comp_mul_right (a (Multiplicative.ofAdd s))) χ).restrict
      · have hconst : ∀ s : ℝ, ∫ x, ‖Function.uncurry (fun (s : ℝ) (x : G) =>
            h (x * a (Multiplicative.ofAdd s)) * star ((χ x : ℂ))) (s, x)‖
              ∂(μ.restrict (Γ₀ : Set G)) = ∫ x, ‖h x‖ ∂μ := by
          intro s
          simp only [Function.uncurry_apply_pair, norm_mul, norm_star, Circle.norm_coe, mul_one]
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
            simp [hvan s x hx])]
          exact integral_mul_right_eq_self (μ := μ) (fun x => ‖h x‖) _
        simp_rw [hconst]
        exact integrable_const _
    rw [← intervalIntegral_integral_swap hint]
    have hinner : ∀ s : ℝ, ∫ x in (Γ₀ : Set G), h (x * a (Multiplicative.ofAdd s)) *
        star ((χ x : ℂ)) ∂μ = e s * RiemannMasullo.lcaFourier μ h χ := by
      intro s
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hvan s x hx])]
      exact htr h s
    simp_rw [hinner]
    rw [intervalIntegral.integral_mul_const, mul_comm]
  -- conclusion
  set F := RiemannMasullo.lcaFourier μ f χ with hF_def
  set H := RiemannMasullo.lcaFourier μ h χ with hH_def
  have hI : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, e s) (e 0) 0 :=
    (he.integral_hasStrictDerivAt 0 0).hasDerivAt
  by_cases hF : F = 0
  · have hH : H = 0 := by
      by_contra hH
      have hz : ∀ t, ∫ s in (0 : ℝ)..t, e s = 0 := fun t => by
        have := hid t
        rw [hF, mul_zero, sub_zero] at this
        exact (mul_eq_zero.1 this.symm).resolve_left hH
      have h0 : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, e s) 0 0 := by
        simp_rw [hz]
        exact hasDerivAt_const _ _
      have := hI.unique h0
      rw [he0] at this
      exact one_ne_zero this
    rw [hF, hH, mul_zero]
  · have hpt : ∀ t, e t = 1 + H / F * ∫ s in (0 : ℝ)..t, e s := by
      intro t
      have := hid t
      field_simp
      linear_combination this
    have hd : HasDerivAt (fun t => 1 + H / F * ∫ s in (0 : ℝ)..t, e s) (H / F * e 0) 0 :=
      (hI.const_mul (H / F)).const_add 1
    have hd' : HasDerivAt e (H / F * e 0) 0 :=
      hd.congr_of_eventuallyEq (Filter.Eventually.of_forall hpt)
    rw [hd'.deriv, he0, mul_one]
    field_simp

end fourier

end Sol_MasulloGRH_schwartzBruhat_fourier_oneParameterDeriv

open MasulloGRH Sol_MasulloGRH_schwartzBruhat_fourier_oneParameterDeriv

theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (a : Multiplicative ℝ →ₜ* G) (f : SchwartzBruhat G) (χ : PontryaginDual G) :
    Integrable (fun g : G => deriv (fun t : ℝ => f (g * a (Multiplicative.ofAdd t))) 0) μ ∧
    RiemannMasullo.lcaFourier μ
        (fun g : G => deriv (fun t : ℝ => f (g * a (Multiplicative.ofAdd t))) 0) χ =
      deriv (fun t : ℝ => ((χ (a (Multiplicative.ofAdd t)) : Circle) : ℂ)) 0 *
        RiemannMasullo.lcaFourier μ (f : G → ℂ) χ := by
  obtain ⟨D, hD⟩ := schwartzBruhat_oneParameterDeriv G a
  have hfun : (fun g : G => deriv (fun t : ℝ => f (g * a (Multiplicative.ofAdd t))) 0) =
      ((D f : SchwartzBruhat G) : G → ℂ) := funext fun g => (hD f g).deriv
  rw [hfun]
  refine ⟨integrable_sb' μ (D f), ?_⟩
  obtain ⟨C₁, hC₁, h₁⟩ := support_closure ((D f : SchwartzBruhat G) : G → ℂ) (D f).2
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds (1 : G)
  have hΓ₀ : IsOpen ((Subgroup.closure (C₁ ∪ V) : Subgroup G) : Set G) :=
    Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset hV
      (fun x hx => Subgroup.subset_closure (Or.inr hx)))
  have : SigmaFinite (μ.restrict ((Subgroup.closure (C₁ ∪ V) : Subgroup G) : Set G)) :=
    sigmaFinite_restrict μ (C₁ ∪ V) (hC₁.union hVc) _ le_rfl
  exact key μ (f : G → ℂ) ((D f : SchwartzBruhat G) : G → ℂ) (integrable_sb' μ f)
    (integrable_sb' μ (D f)) (continuous_sb (D f)) a (hD f)
    (Subgroup.closure (C₁ ∪ V)) hΓ₀
    (fun x hx => h₁ x (fun h' => hx (Subgroup.closure_mono Set.subset_union_left h'))) χ
