-- Prove2me | solution 1 for MeasureTheory.exists_isLocallyConstant_integral_subgroup_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/8e9e2380-a3b5-594a-8a51-656ee9aa14e3

import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_isLocallyConstant_integral_subgroup_mul_eq_one

set_option autoImplicit false

open MeasureTheory

namespace B2Draft

section

open Set

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]

private theorem isLocallyConstant_of_forall_mul_mem {Y : Type*} (K₀ : Subgroup G) (hK₀o : IsOpen (K₀ : Set G))
    (f : G → Y) (hf : ∀ y, ∀ k ∈ K₀, f (y * k) = f y) : IsLocallyConstant f := by
  refine (IsLocallyConstant.iff_exists_open f).2 fun y =>
    ⟨(fun z => y⁻¹ * z) ⁻¹' (K₀ : Set G), hK₀o.preimage (continuous_const_mul y⁻¹), ?_, ?_⟩
  · show y⁻¹ * y ∈ (K₀ : Set G)
    rw [inv_mul_cancel]
    exact K₀.one_mem
  · intro z hz
    have hz' : y⁻¹ * z ∈ K₀ := hz
    calc f z = f (y * (y⁻¹ * z)) := by rw [mul_inv_cancel_left]
      _ = f y := hf y _ hz'

private theorem isClosed_of_forall_mul_mem_iff (K₀ : Subgroup G) (hK₀o : IsOpen (K₀ : Set G)) {C : Set G}
    (hC : ∀ y, ∀ k ∈ K₀, (y * k ∈ C ↔ y ∈ C)) : IsClosed C := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro y hy
  refine ⟨(fun z => y⁻¹ * z) ⁻¹' (K₀ : Set G), ?_, hK₀o.preimage (continuous_const_mul y⁻¹), ?_⟩
  · intro z hz
    have hz' : y⁻¹ * z ∈ K₀ := hz
    show z ∉ C
    intro hzC
    have hyz : y * (y⁻¹ * z) ∈ C := by rwa [mul_inv_cancel_left]
    exact hy ((hC y _ hz').1 hyz)
  · show y⁻¹ * y ∈ (K₀ : Set G)
    rw [inv_mul_cancel]
    exact K₀.one_mem

private theorem exists_lift_set (K₀ : Subgroup G) (hK₀c : IsCompact (K₀ : Set G)) (hK₀o : IsOpen (K₀ : Set G))
    {Ω : Set G} (hΩ : IsCompact Ω) :
    ∃ C : Set G, IsCompact C ∧ IsOpen C ∧ Ω ⊆ C ∧ ∀ y ∈ C, ∀ k ∈ K₀, y * k ∈ C := by
  let U : G → Set G := fun x => (fun y => x⁻¹ * y) ⁻¹' (K₀ : Set G)
  have hUo : ∀ x, IsOpen (U x) := fun x => hK₀o.preimage (continuous_const_mul x⁻¹)
  have hUc : ∀ x, IsCompact (U x) := by
    intro x
    have hx : U x = (fun y => x * y) '' (K₀ : Set G) := by
      ext y
      constructor
      · intro hy
        exact ⟨x⁻¹ * y, hy, mul_inv_cancel_left x y⟩
      · rintro ⟨k, hk, rfl⟩
        show x⁻¹ * (x * k) ∈ (K₀ : Set G)
        rw [inv_mul_cancel_left]
        exact hk
    rw [hx]
    exact hK₀c.image (continuous_const_mul x)
  have hxU : ∀ x, x ∈ U x := by
    intro x
    show x⁻¹ * x ∈ (K₀ : Set G)
    rw [inv_mul_cancel]
    exact K₀.one_mem
  have hUK : ∀ x, ∀ y ∈ U x, ∀ k ∈ K₀, y * k ∈ U x := by
    intro x y hy k hk
    show x⁻¹ * (y * k) ∈ (K₀ : Set G)
    rw [← mul_assoc]
    exact K₀.mul_mem hy hk
  obtain ⟨I, -, hI⟩ := hΩ.elim_nhds_subcover U fun x _ => (hUo x).mem_nhds (hxU x)
  refine ⟨⋃ x ∈ I, U x, I.finite_toSet.isCompact_biUnion fun x _ => hUc x,
    isOpen_biUnion (s := (I : Set G)) fun x _ => hUo x, hI, ?_⟩
  intro y hy k hk
  rw [mem_iUnion₂] at hy ⊢
  obtain ⟨x, hx, hyx⟩ := hy
  exact ⟨x, hx, hUK x y hyx k hk⟩

end

end B2Draft

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K₀ : Subgroup G) (hK₀ : IsCompact (K₀ : Set G)) (hK₀' : IsOpen (K₀ : Set G))
    (T : Subgroup G) (hT : IsClosed (T : Set G)) (hcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    [MeasurableSpace T] [BorelSpace T] (τ : Measure T) [τ.IsHaarMeasure]
    (Ω : Set G) (hΩ : IsCompact Ω) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ IsLocallyConstant w ∧ HasCompactSupport w ∧
      ∀ x : G, (∃ t ∈ T, ∃ d ∈ Ω, x = t * d) → ∫ t : T, w (t * x) ∂τ = 1 := by
  obtain ⟨C, hCc, hCo, hΩC, hCK⟩ := B2Draft.exists_lift_set K₀ hK₀ hK₀' hΩ
  have hCiff : ∀ y, ∀ k ∈ K₀, (y * k ∈ C ↔ y ∈ C) := by
    intro y k hk
    constructor
    · intro h
      have h' := hCK _ h k⁻¹ (K₀.inv_mem hk)
      rwa [mul_inv_cancel_right] at h'
    · intro h
      exact hCK _ h k hk
  have hCcl : IsClosed C := B2Draft.isClosed_of_forall_mul_mem_iff K₀ hK₀' hCiff

  let A : G → Set T := fun y => (fun t : T => (t : G) * y) ⁻¹' C
  have hAo : ∀ y, IsOpen (A y) :=
    fun y => hCo.preimage ((continuous_mul_const y).comp continuous_subtype_val)
  have hAc : ∀ y, IsCompact (A y) := by
    intro y
    have h1 : IsCompact ((fun g : G => g * y) ⁻¹' C) := (Homeomorph.mulRight y).isCompact_preimage.2 hCc
    exact hT.isClosedEmbedding_subtypeVal.isCompact_preimage h1
  have hAtop : ∀ y, τ (A y) ≠ ⊤ := fun y => ((hAc y).measure_lt_top (μ := τ)).ne
  have hAne : ∀ y ∈ C, τ (A y) ≠ 0 := by
    intro y hy
    refine ((hAo y).measure_pos τ ⟨1, ?_⟩).ne'
    show ((1 : T) : G) * y ∈ C
    rw [OneMemClass.coe_one, one_mul]
    exact hy

  have hAK : ∀ y, ∀ k ∈ K₀, A (y * k) = A y := by
    intro y k hk
    ext t
    show (t : G) * (y * k) ∈ C ↔ (t : G) * y ∈ C
    rw [← mul_assoc]
    exact hCiff _ k hk

  have hAT : ∀ (s : T) (y : G), τ (A ((s : G) * y)) = τ (A y) := by
    intro s y
    have h : A ((s : G) * y) = (fun t : T => s * t) ⁻¹' A y := by
      ext t
      show (t : G) * ((s : G) * y) ∈ C ↔ ((s * t : T) : G) * y ∈ C
      rw [Subgroup.coe_mul, ← mul_assoc, hcomm s s.2 t t.2]
    rw [h]
    exact measure_preimage_mul τ s (A y)

  let φ : G → ℝ := fun y => τ.real (A y)
  have hφpos : ∀ y ∈ C, 0 < φ y := by
    intro y hy
    show 0 < (τ (A y)).toReal
    exact ENNReal.toReal_pos (hAne y hy) (hAtop y)
  have hφK : ∀ y, ∀ k ∈ K₀, φ (y * k) = φ y := by
    intro y k hk
    show (τ (A (y * k))).toReal = (τ (A y)).toReal
    rw [hAK y k hk]
  have hφT : ∀ (s : T) (y : G), φ ((s : G) * y) = φ y := by
    intro s y
    show (τ (A ((s : G) * y))).toReal = (τ (A y)).toReal
    rw [hAT s y]

  have hwK : ∀ y, ∀ k ∈ K₀,
      C.indicator (fun z => (φ z)⁻¹) (y * k) = C.indicator (fun z => (φ z)⁻¹) y := by
    intro y k hk
    by_cases hy : y ∈ C
    · have hyk : y * k ∈ C := (hCiff y k hk).2 hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hyk, hφK y k hk]
    · have hyk : y * k ∉ C := fun h => hy ((hCiff y k hk).1 h)
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hyk]
  refine ⟨C.indicator fun z => (φ z)⁻¹, ?_, B2Draft.isLocallyConstant_of_forall_mul_mem K₀ hK₀' _ hwK,
    HasCompactSupport.intro' hCc hCcl fun y hy => Set.indicator_of_notMem hy _, ?_⟩
  · intro x
    exact Set.indicator_nonneg (fun z _ => inv_nonneg.2 ENNReal.toReal_nonneg) x
  · rintro x ⟨t₀, ht₀, d, hd, rfl⟩
    have hdC : d ∈ C := hΩC hd
    have hind : (fun t : T => C.indicator (fun z => (φ z)⁻¹) ((t : G) * (t₀ * d))) =
        (A (t₀ * d)).indicator fun _ => (φ d)⁻¹ := by
      funext t
      by_cases h : (t : G) * (t₀ * d) ∈ C
      · have hA : t ∈ A (t₀ * d) := h
        have hts : (t : G) * (t₀ * d) = ((t * ⟨t₀, ht₀⟩ : T) : G) * d := by
          show (t : G) * (t₀ * d) = (t : G) * t₀ * d
          exact (mul_assoc _ _ _).symm
        rw [Set.indicator_of_mem h, Set.indicator_of_mem hA, hts, hφT]
      · have hA : t ∉ A (t₀ * d) := h
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hA]
    have h2 : τ.real (A (t₀ * d)) = φ d := hφT ⟨t₀, ht₀⟩ d
    rw [hind, integral_indicator_const _ (hAo (t₀ * d)).measurableSet, smul_eq_mul, h2]
    exact mul_inv_cancel₀ (hφpos d hdC).ne'

end S_MeasureTheory_exists_isLocallyConstant_integral_subgroup_mul_eq_one
end P2MW
export P2MW.S_MeasureTheory_exists_isLocallyConstant_integral_subgroup_mul_eq_one (solution)
