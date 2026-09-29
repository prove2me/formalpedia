-- Prove2me | solution 1 for MeasureTheory.sq_norm_apply_mul_measureReal_le_finrank_mul_integral_sq_norm_of_forall_mul_right_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/252d83aa-d794-57cb-b33a-4ce11fcd8b1e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_sq_norm_apply_mul_measureReal_le_finrank_mul_integral_sq_norm_of_forall_mul_right_mem

set_option autoImplicit false

open MeasureTheory Module
open scoped ComplexConjugate InnerProductSpace

namespace RKB

section Haar

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

theorem isMulRightInvariant_of_compactSpace : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h := Measure.map_right_mul_eq_modularCharacterFun_smul μ g
  have hne : μ Set.univ ≠ 0 := (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'
  have htop : μ Set.univ ≠ ⊤ := measure_ne_top μ _
  have h1 := congrArg (fun m : Measure G => m Set.univ) h
  simp only [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ,
    Measure.nnreal_smul_coe_apply] at h1
  have key : ((Measure.modularCharacterFun g : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_eq_left hne htop).mp (by rw [mul_comm]; exact h1.symm)
  have key' : Measure.modularCharacterFun g = 1 := by exact_mod_cast key
  rw [h, key', one_smul]

end Haar

section Core

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  (V : Submodule ℂ (G → ℂ)) (hcont : ∀ f ∈ V, Continuous f)

theorem conj_mul_self_eq (z : ℂ) : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

include hcont in
theorem integrable_conj_mul (u w : G → ℂ) (hu : u ∈ V) (hw : w ∈ V) :
    Integrable (fun x => conj (u x) * w x) μ :=
  ((Complex.continuous_conj.comp (hcont u hu)).mul (hcont w hw)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

include hcont in
theorem integrable_norm_sq (u : G → ℂ) (hu : u ∈ V) :
    Integrable (fun x => ‖u x‖ ^ 2) μ :=
  (((hcont u hu).norm).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

include hcont in
theorem integral_conj_mul_self (u : G → ℂ) (hu : u ∈ V) :
    (∫ x, conj (u x) * u x ∂μ) = ((∫ x, ‖u x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  simp_rw [conj_mul_self_eq]
  exact integral_complex_ofReal

noncomputable def core : InnerProductSpace.Core ℂ V where
  inner u w := ∫ x, conj ((u : G → ℂ) x) * (w : G → ℂ) x ∂μ
  conj_inner_symm u w := by
    show conj (∫ x, conj ((w : G → ℂ) x) * (u : G → ℂ) x ∂μ) =
      ∫ x, conj ((u : G → ℂ) x) * (w : G → ℂ) x ∂μ
    rw [← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_mul, Complex.conj_conj, mul_comm]
  re_inner_nonneg u := by
    show 0 ≤ RCLike.re (∫ x, conj ((u : G → ℂ) x) * (u : G → ℂ) x ∂μ)
    rw [integral_conj_mul_self μ V hcont u u.2, RCLike.re_to_complex, Complex.ofReal_re]
    exact integral_nonneg fun x => by positivity
  add_left u v w := by
    show (∫ x, conj (((u + v : V) : G → ℂ) x) * (w : G → ℂ) x ∂μ) =
      (∫ x, conj ((u : G → ℂ) x) * (w : G → ℂ) x ∂μ) + ∫ x, conj ((v : G → ℂ) x) * (w : G → ℂ) x ∂μ
    rw [← integral_add (integrable_conj_mul μ V hcont _ _ u.2 w.2) (integrable_conj_mul μ V hcont _ _ v.2 w.2)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Submodule.coe_add, Pi.add_apply, map_add, add_mul]
  smul_left u w r := by
    show (∫ x, conj (((r • u : V) : G → ℂ) x) * (w : G → ℂ) x ∂μ) =
      conj r * ∫ x, conj ((u : G → ℂ) x) * (w : G → ℂ) x ∂μ
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
  definite u hu := by
    change (∫ x, conj ((u : G → ℂ) x) * (u : G → ℂ) x ∂μ) = 0 at hu
    rw [integral_conj_mul_self μ V hcont u u.2, Complex.ofReal_eq_zero] at hu
    have h0 : (fun x => ‖(u : G → ℂ) x‖ ^ 2) = 0 := by
      have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) (integrable_norm_sq μ V hcont u u.2)).mp hu
      exact (Continuous.ae_eq_iff_eq μ (((hcont u u.2).norm).pow 2) continuous_const).mp hae
    ext x
    have := congrFun h0 x
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at this
    simp [this]

end Core

section Main

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

theorem main (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V]
    (hcont : ∀ f ∈ V, Continuous f)
    (hinv : ∀ f ∈ V, ∀ g : G, (fun x => f (x * g)) ∈ V)
    (f : G → ℂ) (hf : f ∈ V) (x : G) :
    ‖f x‖ ^ 2 * μ.real Set.univ ≤ (finrank ℂ V : ℝ) * ∫ y, ‖f y‖ ^ 2 ∂μ := by
  haveI : μ.IsMulRightInvariant := isMulRightInvariant_of_compactSpace μ
  letI : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ (core μ V hcont)
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore (core μ V hcont).toCore

  have inner_def : ∀ u w : V, ⟪u, w⟫_ℂ = ∫ y, conj ((u : G → ℂ) y) * (w : G → ℂ) y ∂μ := fun u w => rfl
  have norm_sq_eq : ∀ u : V, ‖u‖ ^ 2 = ∫ y, ‖(u : G → ℂ) y‖ ^ 2 ∂μ := by
    intro u
    rw [@norm_sq_eq_re_inner ℂ, inner_def, integral_conj_mul_self μ V hcont u u.2, RCLike.re_to_complex,
      Complex.ofReal_re]

  let R : G → (V →ₗ[ℂ] V) := fun g =>
    { toFun := fun u => ⟨fun y => (u : G → ℂ) (y * g), hinv u u.2 g⟩
      map_add' := fun u w => by ext y; rfl
      map_smul' := fun c u => by ext y; rfl }
  have hRapply : ∀ (g : G) (u : V) (y : G), ((R g u : V) : G → ℂ) y = (u : G → ℂ) (y * g) := fun g u y => rfl
  have hR : ∀ (g : G) (u w : V), ⟪R g u, R g w⟫_ℂ = ⟪u, w⟫_ℂ := by
    intro g u w
    rw [inner_def, inner_def]
    exact integral_mul_right_eq_self (fun y => conj ((u : G → ℂ) y) * (w : G → ℂ) y) g
  let Rg : G → (V ≃ₗᵢ[ℂ] V) := fun g => (LinearMap.isometryOfInner (R g) (hR g)).toLinearIsometryEquiv rfl
  have hRg : ∀ (g : G) (u : V) (y : G), ((Rg g u : V) : G → ℂ) y = (u : G → ℂ) (y * g) := fun g u y => rfl

  set n := finrank ℂ V with hn
  let vec : OrthonormalBasis (Fin n) ℂ V → G → V := fun c y => ∑ j, conj ((c j : G → ℂ) y) • c j
  let P : OrthonormalBasis (Fin n) ℂ V → G → ℝ := fun c y => ∑ j, ‖(c j : G → ℂ) y‖ ^ 2

  have hA : ∀ (c : OrthonormalBasis (Fin n) ℂ V) (y : G) (w : V), ⟪vec c y, w⟫_ℂ = (w : G → ℂ) y := by
    intro c y w
    simp only [vec, sum_inner, inner_smul_left, Complex.conj_conj]
    have h := congrArg (fun u : V => (u : G → ℂ) y) (c.sum_repr' w)
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

  have hB : ∀ (c : OrthonormalBasis (Fin n) ℂ V) (y : G), ‖vec c y‖ ^ 2 = P c y := by
    intro c y
    rw [@norm_sq_eq_re_inner ℂ, hA c y (vec c y)]
    simp only [vec, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      conj_mul_self_eq]
    rw [← Complex.ofReal_sum, RCLike.re_to_complex, Complex.ofReal_re]

  have hC : ∀ (c c' : OrthonormalBasis (Fin n) ℂ V) (y : G), vec c y = vec c' y := by
    intro c c' y
    refine ext_inner_right ℂ fun w => ?_
    rw [hA, hA]

  have hD : ∀ (c : OrthonormalBasis (Fin n) ℂ V) (y g : G), P c (y * g) = P (c.map (Rg g)) y := by
    intro c y g
    simp only [P, OrthonormalBasis.map_apply, hRg]

  let b : OrthonormalBasis (Fin n) ℂ V := stdOrthonormalBasis ℂ V
  have hconst : ∀ y : G, P b y = P b 1 := by
    intro y
    have h1 := hD b 1 y
    rw [one_mul] at h1
    rw [h1, ← hB, ← hB, hC (b.map (Rg y)) b]

  have hE : (∫ y, P b y ∂μ) = n := by
    simp only [P]
    rw [integral_finsetSum _ fun j _ => integrable_norm_sq μ V hcont _ (b j).2]
    have : ∀ j, (∫ y, ‖((b j : V) : G → ℂ) y‖ ^ 2 ∂μ) = 1 := fun j => by
      rw [← norm_sq_eq, b.orthonormal.1 j, one_pow]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hE' : P b 1 * μ.real Set.univ = n := by
    have h := hE
    simp_rw [hconst] at h
    rw [integral_const, smul_eq_mul] at h
    rw [mul_comm]; exact h

  have hfx : ‖f x‖ ^ 2 ≤ P b x * ∫ y, ‖f y‖ ^ 2 ∂μ := by
    have h := hA b x ⟨f, hf⟩
    have hcs := norm_inner_le_norm (𝕜 := ℂ) (vec b x) (⟨f, hf⟩ : V)
    rw [h] at hcs
    have h2 : ‖f x‖ ^ 2 ≤ (‖vec b x‖ * ‖(⟨f, hf⟩ : V)‖) ^ 2 := by
      have : 0 ≤ ‖f x‖ := norm_nonneg _
      exact pow_le_pow_left₀ this hcs 2
    rw [mul_pow, hB, norm_sq_eq] at h2
    exact h2
  calc ‖f x‖ ^ 2 * μ.real Set.univ ≤ P b x * (∫ y, ‖f y‖ ^ 2 ∂μ) * μ.real Set.univ := by
        gcongr
    _ = (P b 1 * μ.real Set.univ) * ∫ y, ‖f y‖ ^ 2 ∂μ := by rw [hconst x]; ring
    _ = (n : ℝ) * ∫ y, ‖f y‖ ^ 2 ∂μ := by rw [hE']

end Main

end RKB

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V]
    (hcont : ∀ f ∈ V, Continuous f)
    (hinv : ∀ f ∈ V, ∀ g : G, (fun x => f (x * g)) ∈ V) :
    ∀ f ∈ V, ∀ x : G,
      ‖f x‖ ^ 2 * μ.real Set.univ ≤ (Module.finrank ℂ V : ℝ) * ∫ y, ‖f y‖ ^ 2 ∂μ :=
  fun f hf x => RKB.main μ V hcont hinv f hf x

end S_MeasureTheory_sq_norm_apply_mul_measureReal_le_finrank_mul_integral_sq_norm_of_forall_mul_right_mem
end P2MW
export P2MW.S_MeasureTheory_sq_norm_apply_mul_measureReal_le_finrank_mul_integral_sq_norm_of_forall_mul_right_mem (solution)
