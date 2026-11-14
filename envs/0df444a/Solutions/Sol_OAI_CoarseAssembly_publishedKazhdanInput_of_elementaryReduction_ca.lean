-- Prove2me | solution 1 for OAI.CoarseAssembly.publishedKazhdanInput_of_elementaryReduction_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T11:05:04.19857+00:00
-- url     : https://prove2.me/submissions/5346e55d-4c49-4f2f-9095-bf75b1443182

import Mathlib
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.TransferInstance
import Definitions.Def_CoarseAssembly
import Definitions.Def_OAIQ229C036
import Definitions.Def_OAIQ229C037
import Theorems.Thm_OAI_CoarseAssembly_elementaryKernel_projection_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_certificate_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_energy_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_nonneg_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_basis_good_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_delta_good_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_goodWord_inv_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_goodWord_mul_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_residual_augmentation_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_residual_l1_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_row_normalizations_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_support_compress_iff_ca

section
-- module Solutions.Q229_CA.CoarseAssembly_AveragingEnergy
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Energy estimate for the actual lazy averages -/

noncomputable section

namespace CoarseAssembly

open Congruence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem translation_real_inner (k : ℕ) (s : ArithmeticGroup)
    (x : lp (fun _ : Quotient k => H) 2) :
    (inner ℂ x (leftTranslation (Quotient k) (reduce k s) x)).re =
      ‖x‖ ^ 2 - ‖leftTranslation (Quotient k) (reduce k s) x - x‖ ^ 2 / 2 := by
  have h := norm_sub_sq (𝕜 := ℂ) (leftTranslation (Quotient k) (reduce k s) x) x
  rw [(leftTranslation (Quotient k) (reduce k s)).norm_map, inner_re_symm] at h
  change ‖leftTranslation (Quotient k) (reduce k s) x - x‖ ^ 2 =
    ‖x‖ ^ 2 - 2 * (inner ℂ x (leftTranslation (Quotient k) (reduce k s) x)).re + ‖x‖ ^ 2 at h
  linarith

omit [CompleteSpace H] in
theorem meanTranslation_real_inner (S : Finset ArithmeticGroup) (hS : S.Nonempty)
    (k : ℕ) (x : lp (fun _ : Quotient k => H) 2) :
    (inner ℂ x (meanTranslation S k x)).re =
      ‖x‖ ^ 2 - translationEnergy S k x / (2 * S.card) := by
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hm : meanTranslation S k x = (S.card : ℂ)⁻¹ •
      ∑ s ∈ S, leftTranslation (Quotient k) (reduce k s) x := by
    simp only [meanTranslation, smul_apply, sum_apply]
    rfl
  rw [hm, inner_smul_right]
  have hc : (S.card : ℂ)⁻¹ = ((S.card : ℝ)⁻¹ : ℂ) := by simp
  rw [hc]
  simp only [← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    inner_sum, Complex.re_sum, translation_real_inner, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div]
  unfold translationEnergy
  field_simp

/-- Laziness turns the displacement-energy bound into a norm-square loss. -/
theorem lazyAverage_norm_sq_le (S : Finset ArithmeticGroup) (hS : S.Nonempty)
    (k : ℕ) (x : lp (fun _ : Quotient k => H) 2) :
    ‖lazyAverage S k x‖ ^ 2 ≤
      ‖x‖ ^ 2 - translationEnergy S k x / (4 * S.card) := by
  have hm : ‖meanTranslation S k x‖ ≤ ‖x‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (meanTranslation_norm_le S k))
  have he := meanTranslation_real_inner S hS k x
  have ha : lazyAverage S k x = (1 / 2 : ℂ) • (x + meanTranslation S k x) := rfl
  rw [ha, norm_smul, mul_pow, norm_add_sq (𝕜 := ℂ)]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  have hdiv : translationEnergy S k x / (4 * S.card) =
      (translationEnergy S k x / (2 * S.card)) / 2 := by ring
  rw [hdiv]
  change ‖meanTranslation S k x‖ ≤ ‖x‖ at hm
  change RCLike.re (inner ℂ x (meanTranslation S k x)) =
    ‖x‖ ^ 2 - translationEnergy S k x / (2 * S.card) at he
  nlinarith [norm_nonneg (meanTranslation S k x), norm_nonneg x]

variable (Q : Type*) [Fintype Q] [Nonempty Q]

theorem constantProjection_complement_zero (x : lp (fun _ : Q => H) 2) :
    constantProjection Q (x - constantProjection Q x) = 0 := by
  rw [map_sub]
  have h := DFunLike.congr_fun (constantProjection_idempotent (H := H) Q) x
  change constantProjection Q (constantProjection Q x) = constantProjection Q x at h
  rw [h, sub_self]

theorem constantProjection_complement_norm_le (x : lp (fun _ : Q => H) 2) :
    ‖x - constantProjection Q x‖ ≤ ‖x‖ := by
  let U := (fiberConstantIsometry (H := H) Q).toContinuousLinearMap
  have hi : inner ℂ x (constantProjection Q x) = inner ℂ (U.adjoint x) (U.adjoint x) := by
    exact (ContinuousLinearMap.adjoint_inner_left U (U.adjoint x) x).symm
  have hn : ‖constantProjection Q x‖ = ‖U.adjoint x‖ :=
    (fiberConstantIsometry (H := H) Q).norm_map (U.adjoint x)
  have hs := norm_sub_sq (𝕜 := ℂ) x (constantProjection Q x)
  change ‖x - constantProjection Q x‖ ^ 2 =
    ‖x‖ ^ 2 - 2 * (inner ℂ x (constantProjection Q x)).re + ‖constantProjection Q x‖ ^ 2 at hs
  have hr : (inner ℂ (U.adjoint x) (U.adjoint x)).re = ‖U.adjoint x‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (U.adjoint x)).symm
  rw [hi, hn, hr] at hs
  nlinarith [norm_nonneg (x - constantProjection Q x), norm_nonneg x,
    sq_nonneg ‖U.adjoint x‖]

/-- A uniform energy estimate off the constants implies the precise norm
contraction used by the spatial transfer. -/
theorem uniformAveragingGap_of_energy (S : Finset ArithmeticGroup) (hS : S.Nonempty)
    (ε : ℝ) (hε : 0 < ε) (hεcard : ε ≤ 4 * S.card)
    (henergy : ∀ (k : ℕ) (x : lp (fun _ : Quotient k => H) 2),
      constantProjection (Quotient k) x = 0 →
        ε * ‖x‖ ^ 2 ≤ translationEnergy S k x) : UniformAveragingGap S H := by
  have hd : 0 < (4 : ℝ) * S.card := mul_pos (by norm_num) (by exact_mod_cast hS.card_pos)
  have hdv : 0 < ε / (4 * S.card) := div_pos hε hd
  have hn : 0 ≤ 1 - ε / (4 * S.card) := sub_nonneg.mpr ((div_le_one hd).2 hεcard)
  let c := Real.sqrt (1 - ε / (4 * S.card))
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hcs : c ^ 2 = 1 - ε / (4 * S.card) := Real.sq_sqrt hn
  have hclt : c < 1 := by nlinarith
  have hb (k : ℕ) (x : lp (fun _ : Quotient k => H) 2)
      (hx : constantProjection (Quotient k) x = 0) : ‖lazyAverage S k x‖ ≤ c * ‖x‖ := by
    have hl := lazyAverage_norm_sq_le S hS k x
    have he := div_le_div_of_nonneg_right (henergy k x hx) hd.le
    have heq : ε * ‖x‖ ^ 2 / (4 * S.card) = (ε / (4 * S.card)) * ‖x‖ ^ 2 := by ring
    rw [heq] at he
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).1
    rw [mul_pow, hcs]
    nlinarith
  refine ⟨c, hc, hclt, ?_⟩
  intro k
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  let y := x - constantProjection (Quotient k) x
  have hy : constantProjection (Quotient k) y = 0 := constantProjection_complement_zero _ x
  have hm := DFunLike.congr_fun (lazyAverage_projection (H := H) S hS k) x
  change lazyAverage S k (constantProjection (Quotient k) x) = constantProjection (Quotient k) x at hm
  have heq : (lazyAverage (H := H) S k - constantProjection (H := H) (Quotient k)) x = lazyAverage S k y := by
    change lazyAverage S k x - constantProjection (Quotient k) x =
      lazyAverage S k (x - constantProjection (Quotient k) x)
    rw [map_sub, hm]
  rw [heq]
  exact (hb k y hy).trans (mul_le_mul_of_nonneg_left (constantProjection_complement_norm_le _ x) hc)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RegularConstants
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invariants of the actual amplified finite regular representation -/

noncomputable section

namespace CoarseAssembly

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (Q : Type*) [Fintype Q] [Group Q]

/-- The kernel of the constant projection is orthogonal to every invariant
vector of the regular representation. -/
theorem inner_eq_zero_of_projection_zero (x y : lp (fun _ : Q => H) 2)
    (hx : constantProjection Q x = 0) (hy : constantProjection Q y = y) :
    inner ℂ y x = 0 := by
  let U := (fiberConstantIsometry (H := H) Q).toContinuousLinearMap
  have hax : U.adjoint x = 0 := by
    apply (fiberConstantIsometry (H := H) Q).injective
    change constantProjection Q x = (fiberConstantIsometry (H := H) Q) 0
    simpa only [map_zero] using hx
  calc
    inner ℂ y x = inner ℂ (constantProjection Q y) x := by rw [hy]
    _ = inner ℂ (U.adjoint y) (U.adjoint x) :=
      (ContinuousLinearMap.adjoint_inner_right U (U.adjoint y) x).symm
    _ = 0 := by rw [hax, inner_zero_right]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSSemantics
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
variable {α A : Type*} [DecidableEq α]

theorem support_normalize_iff (le : α → α → Bool) (ps : Poly α) (g : α) :
    g ∈ (normalize le ps).map Prod.fst ↔ g ∈ ps.map Prod.fst := by
  rw [normalize, support_compress_iff_ca]
  exact ((List.perm_insertionSort _ ps).map Prod.fst).mem_iff

end NuclearUltrapower.SOS

end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_IntegerMatrices
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry _root_.OAI.NuclearUltrapower.Elementary.integralTheta_left _root_.OAI.NuclearUltrapower.Elementary.integralTheta_pow_translation _root_.OAI.NuclearUltrapower.Elementary.integralTheta_right _root_.OAI.NuclearUltrapower.Elementary.integralTheta_translation _root_.OAI.NuclearUltrapower.Elementary.residuePermutation_apply _root_.OAI.NuclearUltrapower.Elementary.residueUnitary_apply _root_.OAI.NuclearUltrapower.Elementary.residue_one _root_.OAI.NuclearUltrapower.Elementary.residue_theta _root_.OAI.NuclearUltrapower.SOS.ElementarySpectral.unitaryRep_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace NuclearUltrapower.SOS

theorem generators_det : ∀ m ∈ generators, (toMatrix m).det = 1 := by
  decide +kernel

theorem goodWord_generator {m : Mat3} (hm : m ∈ generators) : GoodWord 1 m := by
  refine ⟨generators_det m hm, [interpret m], by simp, by simp, ?_⟩
  intro s hs
  have : s = interpret m := by simpa using hs
  subst s
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨m, hm, rfl⟩)

theorem goodWord_mono {n k : ℕ} {a : Mat3} (ha : GoodWord n a) (h : n ≤ k) : GoodWord k a := by
  obtain ⟨had, w, hw, hl, hs⟩ := ha
  exact ⟨had, w, hw, hl.trans h, hs⟩

end NuclearUltrapower.SOS
end
end

section

noncomputable section
namespace NuclearUltrapower.SOS

theorem goodWord_mem {n : ℕ} {m : Mat3} (h : GoodWord n m) : interpret m ∈ elementary := by
  obtain ⟨_, w, hw, _, hs⟩ := h
  rw [← hw]
  exact elementary.list_prod_mem (fun g hg => Subgroup.subset_closure (hs g hg))

theorem eInterpret_coe {n : ℕ} {m : Mat3} (h : GoodWord n m) :
    (eInterpret m : SL) = interpret m := by
  simp only [eInterpret, dite_eq_left (goodWord_mem h)]

theorem mem_eGenSet {g : E} : g ∈ eGenSet ↔ (g : SL) ∈ genSet := by
  constructor
  · intro h
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    rw [eInterpret_coe (goodWord_generator hm)]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨m,hm,rfl⟩)
  · intro h
    obtain ⟨m, hm, he⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    apply List.mem_toFinset.mpr
    refine List.mem_map.mpr ⟨m,hm,?_⟩
    apply Subtype.ext
    exact (eInterpret_coe (goodWord_generator hm)).trans he

theorem eWord {n : ℕ} {m : Mat3} (h : GoodWord n m) :
    ∃ w : List E, w.prod = eInterpret m ∧ w.length ≤ n ∧ ∀ s ∈ w, s ∈ eGenSet := by
  obtain ⟨hd,w,hw,hlen,hmem⟩ := h
  let f (s : {s // s ∈ w}) : E := ⟨s.1, Subgroup.subset_closure (hmem _ s.2)⟩
  refine ⟨w.attach.map f, ?_, by simpa using hlen, ?_⟩
  · apply Subtype.ext
    change elementary.subtype ((w.attach.map f).prod) = (eInterpret m : SL)
    rw [map_list_prod, List.map_map]
    simp only [Function.comp_def]
    have he : w.attach.map (fun s => elementary.subtype (f s)) = w := by
      simpa only [f, Subgroup.coe_subtype, List.map_id_fun, id_eq] using
        (List.attach_map_val (l := w) (f := id))
    rw [he, hw, eInterpret_coe ⟨hd,w,hw,hlen,hmem⟩]
  · intro s hs
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hs
    exact mem_eGenSet.mpr (hmem _ t.2)

end NuclearUltrapower.SOS
end
end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSGap
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionMetric _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.SOSEnergy
variable {Γ H : Type*} [Group Γ] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

theorem energy_nonneg (S : Finset Γ) (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    0 ≤ energy S ρ x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Telescoping a word uses only the unitary relations and the specified generators. -/
theorem word_norm_bound (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H) (r : ℝ)
    (w : List Γ) (hw : ∀ s ∈ w, ‖ρ s x - x‖ ≤ r) :
    ‖ρ w.prod x - x‖ ≤ w.length * r := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have ha := hw a (by simp)
    have ht := ih (fun s hs => hw s (by simp [hs]))
    have he : ρ (a * w.prod) x - x =
        ρ a (ρ w.prod x - x) + (ρ a x - x) := by
      rw [map_mul]
      change ρ a (ρ w.prod x) - x = _
      rw [map_sub]
      abel
    simp only [List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [he]
    calc
      _ ≤ ‖ρ a (ρ w.prod x - x)‖ + ‖ρ a x - x‖ := norm_add_le _ _
      _ = ‖ρ w.prod x - x‖ + ‖ρ a x - x‖ := by rw [(ρ a).norm_map]
      _ ≤ w.length * r + r := add_le_add ht ha
      _ = _ := by ring

/-- A length-at-most-four word has energy bounded by sixteen times the generator energy. -/
theorem word_sq_bound (S : Finset Γ) (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (w : List Γ) (hw : ∀ s ∈ w, s ∈ S) (hlen : w.length ≤ 4) :
    ‖ρ w.prod x - x‖ ^ 2 ≤ 16 * energy S ρ x := by
  have he := energy_nonneg S ρ x
  have hb : ∀ s ∈ w, ‖ρ s x - x‖ ≤ Real.sqrt (energy S ρ x) := by
    intro s hs
    apply (Real.le_sqrt (norm_nonneg _) he).mpr
    exact Finset.single_le_sum (fun t _ => sq_nonneg ‖ρ t x - x‖) (hw s hs)
  have hn := word_norm_bound ρ x _ w hb
  have h4 : (w.length : ℝ) ≤ 4 := by exact_mod_cast hlen
  have hn' : ‖ρ w.prod x - x‖ ≤ 4 * Real.sqrt (energy S ρ x) :=
    hn.trans (mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg _))
  nlinarith [Real.sq_sqrt he, norm_nonneg (ρ w.prod x - x), Real.sqrt_nonneg (energy S ρ x)]

/-- The exact real quadratic form of a unitary displacement. -/
theorem real_inner_unitary (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (g : Γ) (x : H) :
    (inner ℂ x (ρ g x)).re = ‖x‖ ^ 2 - ‖ρ g x - x‖ ^ 2 / 2 := by
  have h := norm_sub_sq (𝕜 := ℂ) (ρ g x) x
  rw [(ρ g).norm_map, inner_re_symm] at h
  change ‖ρ g x - x‖ ^ 2 = ‖x‖ ^ 2 - 2 * (inner ℂ x (ρ g x)).re + ‖x‖ ^ 2 at h
  linarith

theorem polyVector_real_inner (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H) (p : List (Γ × ℤ)) :
    (inner ℂ x (polyVector ρ x p)).re =
      ((p.map Prod.snd).sum : ℤ) * ‖x‖ ^ 2 -
        (p.map (fun a => (a.2 : ℝ) * ‖ρ a.1 x - x‖ ^ 2)).sum / 2 := by
  induction p with
  | nil => simp [polyVector]
  | cons a p ih =>
    have hz : (inner ℂ x (a.2 • ρ a.1 x)).re =
        (a.2 : ℝ) * (inner ℂ x (ρ a.1 x)).re := by
      change reInnerAdd x (a.2 • ρ a.1 x) = _
      rw [map_zsmul, zsmul_eq_mul]
      rfl
    simp only [polyVector, List.map_cons, List.sum_cons, inner_add_right,
      Complex.add_re] at ih ⊢
    rw [hz, ih, real_inner_unitary]
    push_cast
    ring

/-- An integer coefficient may have either sign; absolute coefficients suffice. -/
theorem weighted_displacement_le (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (p : List (Γ × ℤ)) (M : ℝ)
    (hb : ∀ a ∈ p, ‖ρ a.1 x - x‖ ^ 2 ≤ M) :
    (p.map (fun a => (a.2 : ℝ) * ‖ρ a.1 x - x‖ ^ 2)).sum ≤
      ((p.map (fun a => |a.2|)).sum : ℤ) * M := by
  induction p with
  | nil => simp
  | cons a p ih =>
    have ht := ih (fun b h => hb b (by simp [h]))
    have h1 : (a.2 : ℝ) * ‖ρ a.1 x - x‖ ^ 2 ≤ |(a.2 : ℝ)| * M :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hb a (by simp)) (abs_nonneg _))
    simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_abs]
    nlinarith

/-- Exact augmentation zero converts a short supported residual into an energy error.
The constant eight here combines the squared word bound 16 with the factor 1/2. -/
theorem residual_lower (S : Finset Γ) (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (p : List (Γ × ℤ)) (haug : (p.map Prod.snd).sum = 0)
    (hsupp : ∀ a ∈ p, ∃ w : List Γ, w.prod = a.1 ∧ w.length ≤ 4 ∧ ∀ s ∈ w, s ∈ S) :
    -(8 * ((p.map (fun a => |a.2|)).sum : ℤ) * energy S ρ x) ≤
      (inner ℂ x (polyVector ρ x p)).re := by
  have hb := weighted_displacement_le ρ x p (16 * energy S ρ x) (by
    intro a ha
    rcases hsupp a ha with ⟨w, hprod, hlen, hw⟩
    rw [← hprod]
    exact word_sq_bound S ρ x w hw hlen)
  rw [polyVector_real_inner, haug, Int.cast_zero, zero_mul, zero_sub]
  nlinarith

end NuclearUltrapower.SOSEnergy

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace NuclearUltrapower
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A sums-of-squares inequality for a positive operator produces a true gap
on the orthogonal complement of its kernel; no finite-dimensional hypothesis. -/
theorem positive_sq_gap (T : H →L[ℂ] H) (hT : 0 ≤ T) (κ : ℝ)
    (hgap : κ • T ≤ T*T) (x : H) (hx : x ∈ T.kerᗮ) :
    κ * ‖x‖ ^ 2 ≤ (inner ℂ x (T x)).re := by
  let R := CFC.sqrt T
  have hR : IsSelfAdjoint R := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)
  have hRR : R * R = T := CFC.sqrt_mul_sqrt_self T hT
  have hRnorm (y : H) : ‖R y‖ ^ 2 = (inner ℂ y (T y)).re := by
    rw [← hRR, mul_apply_eq_comp]
    have hr := hR.isSymmetric y (R y)
    change inner ℂ (R y) (R y) = inner ℂ y (R (R y)) at hr
    rw [← hr]
    exact norm_sq_eq_re_inner (𝕜 := ℂ) (R y)
  have hker : R.ker = T.ker := by
    ext y
    change R y = 0 ↔ T y = 0
    constructor
    · intro h; rw [← hRR, mul_apply_eq_comp, h, map_zero]
    · intro h
      apply norm_eq_zero.mp
      have hn := hRnorm y
      rw [h, inner_zero_right, Complex.zero_re] at hn
      nlinarith [norm_nonneg (R y)]
  have hd : R.range.topologicalClosure = T.kerᗮ := by
    rw [← hker, R.orthogonal_ker]
    congr 1
    exact congrArg (fun A : H →L[ℂ] H => A.toLinearMap.range) hR.star_eq.symm
  have hc : IsClosed {y : H | κ * ‖y‖ ^ 2 ≤ (inner ℂ y (T y)).re} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hs : (R.range : Set H) ⊆ {y : H | κ * ‖y‖ ^ 2 ≤ (inner ℂ y (T y)).re} := by
    rintro _ ⟨y, rfl⟩
    change κ * ‖R y‖ ^ 2 ≤ (inner ℂ (R y) (T (R y))).re
    have hp := ((ContinuousLinearMap.le_def _ _).mp hgap).re_inner_nonneg_right y
    have hTy : T (R y) = R (T y) := by
      rw [← hRR]
      simp only [mul_apply_eq_comp]
    have hr := hR.isSymmetric (R y) (T y)
    change inner ℂ (R (R y)) (T y) = inner ℂ (R y) (R (T y)) at hr
    rw [hRnorm, hTy, ← hr, ← mul_apply_eq_comp, hRR]
    apply sub_nonneg.mp
    change 0 ≤ (inner ℂ y ((T*T - κ • T) y)).re at hp
    have ht := (IsSelfAdjoint.of_nonneg hT).isSymmetric y (T y)
    change inner ℂ (T y) (T y) = inner ℂ y (T (T y)) at ht
    simpa only [sub_apply, mul_apply_eq_comp, smul_apply, inner_sub_right,
      inner_smul_right_eq_smul, Complex.sub_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, ← ht] using hp
  apply (closure_minimal hs hc)
  change x ∈ (R.range.topologicalClosure : Set H)
  rwa [hd]
end NuclearUltrapower

namespace NuclearUltrapower.SOSEnergy
open scoped ComplexOrder
variable {Γ H : Type*} [Group Γ] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem polyOperator_apply (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (p : List (Γ × ℤ)) (x : H) :
    polyOperator ρ p x = polyVector ρ x p := by
  induction p with
  | nil => simp [polyOperator, polyVector]
  | cons a p ih => simpa only [polyOperator, polyVector, List.map_cons, List.sum_cons,
      add_apply, smul_apply, LinearIsometryEquiv.coe_coe''] using (congrArg (fun y : H => a.2 • ρ a.1 x + y) ih)

/-- The rational certificate's defect absorption, with its exact denominator and
certified l1 size. The support/augmentation premises will be discharged by the
matrix-labelled reflection certificate, never assumed of the main group. -/
theorem certificate_sq_gap (S : Finset Γ) (ρ : Γ →* (H ≃ₗᵢ[ℂ] H))
    (D Q : H →L[ℂ] H) (p : List (Γ × ℤ))
    (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (henergy : ∀ x, (inner ℂ x (D x)).re = energy S ρ x / 2)
    (haug : (p.map Prod.snd).sum = 0)
    (hl1 : (p.map (fun a => |a.2|)).sum = 29562852800)
    (hsupp : ∀ a ∈ p, ∃ w : List Γ, w.prod = a.1 ∧ w.length ≤ 4 ∧ ∀ s ∈ w, s ∈ S)
    (hcert : (10000000000000 : ℝ) • (D*D) - (1000000000000 : ℝ) • D =
      Q + polyOperator ρ p) : (1 / 20 : ℝ) • D ≤ D*D := by
  have hself := IsSelfAdjoint.of_nonneg hD
  have hsq : IsSelfAdjoint (D*D) := by simpa only [pow_two] using hself.pow 2
  have hs : IsSelfAdjoint (D*D - (1/20 : ℝ) • D) :=
    hsq.sub ((IsSelfAdjoint.all (1/20 : ℝ)).smul hself)
  apply (ContinuousLinearMap.le_def _ _).mpr
  refine ⟨hs.isSymmetric, ?_⟩
  intro x
  have hr := residual_lower S ρ x p haug hsupp
  rw [hl1] at hr
  have hq := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hQ).re_inner_nonneg_right x
  have hd := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hD).re_inner_nonneg_right x
  have hc := congrArg (fun T : H →L[ℂ] H => (inner ℂ x (T x)).re) hcert
  simp only [sub_apply, smul_apply, add_apply, inner_sub_right, inner_add_right,
    inner_smul_right_eq_smul, Complex.sub_re, Complex.add_re, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    polyOperator_apply] at hc
  change 0 ≤ (inner ℂ ((D*D - (1/20 : ℝ) • D) x) x).re
  change 0 ≤ RCLike.re (inner ℂ ((D*D - (1/20 : ℝ) • D) x) x)
  rw [inner_re_symm (𝕜 := ℂ)]
  change 0 ≤ (inner ℂ x ((D*D - (1/20 : ℝ) • D) x)).re
  simp only [sub_apply, smul_apply, inner_sub_right, inner_smul_right_eq_smul,
    Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  change 0 ≤ (inner ℂ x (D x)).re at hd
  change 0 ≤ (inner ℂ x (Q x)).re at hq
  rw [henergy] at hc hd ⊢
  norm_num at hr
  nlinarith

end NuclearUltrapower.SOSEnergy
end
end
end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry _root_.OAI.NuclearUltrapower.Elementary.integralTheta_left _root_.OAI.NuclearUltrapower.Elementary.integralTheta_pow_translation _root_.OAI.NuclearUltrapower.Elementary.integralTheta_right _root_.OAI.NuclearUltrapower.Elementary.integralTheta_translation _root_.OAI.NuclearUltrapower.Elementary.residuePermutation_apply _root_.OAI.NuclearUltrapower.Elementary.residueUnitary_apply _root_.OAI.NuclearUltrapower.Elementary.residue_one _root_.OAI.NuclearUltrapower.Elementary.residue_theta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SL3Certificate
variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]

theorem dot_eq_sum_getD (N : ℕ) (q r : List ℤ) (hq : q.length ≤ N) (hr : r.length ≤ N) :
    dot q r = ∑ k ∈ Finset.range N, q.getD k 0 * r.getD k 0 := by
  induction N generalizing q r with
  | zero =>
    have hq' : q = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hq)
    have hr' : r = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hr)
    simp [hq', hr']
  | succ N ih =>
    cases q with
    | nil => simp
    | cons a q =>
      cases r with
      | nil => simp
      | cons b r =>
        rw [dot, ih q r (by simpa using hq) (by simpa using hr), Finset.sum_range_succ']
        simp [add_comm]

omit [PartialOrder A] [StarOrderedRing A] in
theorem star_list_sum (v : List A) : star v.sum = (v.map star).sum := by
  induction v with
  | nil => simp
  | cons a v ih => simp [ih]

omit [StarRing A] [PartialOrder A] [StarOrderedRing A] in
theorem list_sum_finset {ι J : Type*} (v : List ι) (s : Finset J) (f : ι → J → A) :
    (v.map (fun i => ∑ k ∈ s, f i k)).sum = ∑ k ∈ s, (v.map (fun i => f i k)).sum := by
  induction v with
  | nil => simp
  | cons a v ih => simp [ih, Finset.sum_add_distrib]

omit [PartialOrder A] [StarOrderedRing A] in
theorem list_gram_identity (N : ℕ) (v : List (A × List ℤ))
    (h : ∀ p ∈ v, p.2.length ≤ N) :
    (v.map (fun p => (v.map (fun q => dot p.2 q.2 • (star p.1 * q.1))).sum)).sum =
      ∑ k ∈ Finset.range N,
        star ((v.map (fun p => (p.2.getD k 0) • p.1)).sum) *
          ((v.map (fun p => (p.2.getD k 0) • p.1)).sum) := by
  have hm (n m : ℤ) (x y : A) : (n*m) • (x*y) = (n • x) * (m • y) := by
    simp only [zsmul_eq_mul, Int.cast_mul, mul_assoc]
    rw [← mul_assoc x (m : A) y, ← (Int.cast_commute m x).eq, mul_assoc]
  have hdot : (v.map (fun p => (v.map (fun q => dot p.2 q.2 • (star p.1 * q.1))).sum)).sum =
      (v.map (fun p => (v.map (fun q =>
        ∑ k ∈ Finset.range N, (p.2.getD k 0 • star p.1) * (q.2.getD k 0 • q.1))).sum)).sum := by
    congr 1
    apply List.map_congr_left
    intro p hp
    congr 1
    apply List.map_congr_left
    intro q hq
    rw [dot_eq_sum_getD N _ _ (h p hp) (h q hq), Finset.sum_smul]
    simp only [hm]
  rw [hdot]
  simp only [list_sum_finset]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [List.sum_map_mul_left, List.sum_map_mul_right, star_list_sum,
    List.map_map, Function.comp_def, star_zsmul]

theorem list_gram_nonneg (N : ℕ) (v : List (A × List ℤ))
    (h : ∀ p ∈ v, p.2.length ≤ N) :
    0 ≤ (v.map (fun p => (v.map (fun q => dot p.2 q.2 • (star p.1 * q.1))).sum)).sum := by
  rw [list_gram_identity N v h]
  exact Finset.sum_nonneg (fun _ _ => star_mul_self_nonneg _)
end NuclearUltrapower.SL3Certificate
end

section

namespace NuclearUltrapower.SOS
open NuclearUltrapower.SL3Certificate

theorem residualRows_decomp : residualRows = residualRow0 :: residualRow1 ::
    (basis.zip gramData).map (fun p => gramPolyRow p.1 p.2) := by rfl

theorem columns_length : columns.map List.length = List.replicate 121 120 := by decide +kernel

theorem columns_bound : ∀ q ∈ columns, q.length ≤ 120 := by
  intro q hq
  have h := List.mem_map_of_mem (f := List.length) hq
  rw [columns_length] at h
  have : q.length = 120 := (List.mem_replicate.mp h).2
  omega

section Operator
variable {A : Type*} [Ring A] [StarRing A]

theorem gramValue_nonneg [PartialOrder A] [StarOrderedRing A] (f : Mat3 → A) :
    0 ≤ gramValue f := by
  have h := list_gram_nonneg 120
    (rootPairs.map (fun p => (f p.1, p.2))) (by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      exact columns_bound q.2 (List.of_mem_zip hq).2)
  simpa only [gramValue, List.map_map, Function.comp_def] using h

end Operator
end NuclearUltrapower.SOS
end

section
namespace NuclearUltrapower.SOS
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem mem_getD_flatten {a : α} (rs : List (List α)) (n : ℕ) (h : a ∈ rs.getD n []) :
    a ∈ rs.flatten := by
  induction rs generalizing n with
  | nil => simp at h
  | cons r rs ih =>
    cases n with
    | zero => exact List.mem_append_left _ (by simpa using h)
    | succ n => exact List.mem_append_right _ (ih n (by simpa using h))

theorem bucket_support_original (le : α → α → Bool)
    (original : List (Poly α)) (buckets : List (List (Poly α)))
    (hnorm : original.map (normalize le) = buckets.map (fun r => normalize le r.flatten))
    (b : ℕ) {m : α}
    (hm : m ∈ (normalize le (buckets.flatMap (fun r => r.getD b []))).map Prod.fst) :
    m ∈ original.flatten.map Prod.fst := by
  have hm' := (support_normalize_iff le _ m).mp hm
  obtain ⟨p, hp, hpval⟩ := List.mem_map.mp hm'
  obtain ⟨r, hr, hpr⟩ := List.mem_flatMap.mp hp
  have hpr' : p ∈ r.flatten := mem_getD_flatten r b hpr
  have hn : normalize le r.flatten ∈ original.map (normalize le) := by
    rw [hnorm]
    exact List.mem_map_of_mem hr
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hn
  have hmnorm : m ∈ (normalize le r.flatten).map Prod.fst :=
    (support_normalize_iff le _ m).mpr (List.mem_map.mpr ⟨p,hpr',hpval⟩)
  rw [← heq] at hmnorm
  have hmq := (support_normalize_iff le q m).mp hmnorm
  obtain ⟨t, ht, htval⟩ := List.mem_map.mp hmq
  exact List.mem_map.mpr ⟨t, List.mem_flatten.mpr ⟨q,hq,ht⟩, htval⟩
end NuclearUltrapower.SOS

namespace NuclearUltrapower.SOS

theorem residualRow0_good {p : Mat3 × ℤ} (hp : p ∈ residualRow0) : GoodWord 4 p.1 := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  obtain ⟨a,ha,hqa⟩ := List.mem_flatMap.mp hq
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hqa
  exact goodWord_mono (goodWord_mul_ca (delta_good_ca ha) (delta_good_ca hb)) (by norm_num)

theorem residualRow1_good {p : Mat3 × ℤ} (hp : p ∈ residualRow1) : GoodWord 4 p.1 := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact goodWord_mono (delta_good_ca (p := q) hq) (by norm_num)

theorem gramPolyRow_good {a : Mat3} (ha : a ∈ basis) (r : List ℤ)
    {p : Mat3 × ℤ} (hp : p ∈ gramPolyRow a r) : GoodWord 4 p.1 := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact goodWord_mul_ca (goodWord_inv_ca (basis_good_ca ha)) (basis_good_ca (List.of_mem_zip hq).1)

theorem residualRows_good {p : Mat3 × ℤ} (hp : p ∈ residualRows.flatten) : GoodWord 4 p.1 := by
  rw [residualRows_decomp] at hp
  simp only [List.flatten_cons, List.mem_append] at hp
  rcases hp with h | h | h
  · exact residualRow0_good h
  · exact residualRow1_good h
  · obtain ⟨r,hr,hp⟩ := List.mem_flatten.mp h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    exact gramPolyRow_good (List.of_mem_zip hq).1 q.2 hp

theorem residual_good {p : Mat3 × ℤ} (hp : p ∈ residual) : GoodWord 4 p.1 := by
  change p ∈ (List.range 128).flatMap residualBucket at hp
  obtain ⟨b,_,hb⟩ := List.mem_flatMap.mp hp
  have h := bucket_support_original matLe residualRows allRowBuckets row_normalizations_ca b
    (List.mem_map_of_mem (f := Prod.fst) hb)
  obtain ⟨q,hq,he⟩ := List.mem_map.mp h
  rw [← he]
  exact residualRows_good hq

end NuclearUltrapower.SOS
end

section

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace NuclearUltrapower.SOS.ElementarySpectral

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem residualInE_aug : (residualInE.map Prod.snd).sum = 0 := by
  simpa only [residualInE, List.map_map, Function.comp_def, augmentation] using residual_augmentation_ca

theorem residualInE_l1 : (residualInE.map (fun p => |p.2|)).sum = 29562852800 := by
  simpa only [residualInE, List.map_map, Function.comp_def, intL1] using residual_l1_ca

theorem residualInE_support : ∀ p ∈ residualInE, ∃ w : List E,
    w.prod = p.1 ∧ w.length ≤ 4 ∧ ∀ s ∈ w, s ∈ eGenSet := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact eWord (residual_good hq)

theorem gramOp_nonneg (ρ : E →* (H ≃ₗᵢ[ℂ] H)) : 0 ≤ gramOp ρ :=
  zsmul_nonneg (gramValue_nonneg _) (by norm_num)

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

section

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace NuclearUltrapower.SOS.ElementarySpectral
section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local irreducible] gramValue eval residual

theorem deltaOp_sq_gap (ρ : E →* (H ≃ₗᵢ[ℂ] H)) :
    (1/20 : ℝ) • deltaOp ρ ≤ deltaOp ρ * deltaOp ρ :=
  SOSEnergy.certificate_sq_gap eGenSet ρ (deltaOp ρ) (gramOp ρ) residualInE
    (deltaOp_nonneg_ca ρ) (gramOp_nonneg ρ) (deltaOp_energy_ca ρ) residualInE_aug
    residualInE_l1 residualInE_support (deltaOp_certificate_ca ρ)

theorem deltaOp_gap (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hx : x ∈ (deltaOp ρ).kerᗮ) :
    (1/10 : ℝ) * ‖x‖ ^ 2 ≤ SOSEnergy.energy eGenSet ρ x := by
  have h := positive_sq_gap (deltaOp ρ) (deltaOp_nonneg_ca ρ) (1/20) (deltaOp_sq_gap ρ) x hx
  rw [deltaOp_energy_ca] at h
  linarith

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CongruenceSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the integral spectral certificate to the finite congruence fibers

The required gap follows from surjectivity of elementary reduction.
-/

noncomputable section

namespace CoarseAssembly

open Congruence
open NuclearUltrapower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem certificateGenerators_subset : SOS.genSet ⊆ elementaryMoves := by
  decide +kernel

omit [CompleteSpace H] in
theorem elementaryEnergy_le (k : ℕ) (x : lp (fun _ : Congruence.Quotient k => H) 2) :
    SOSEnergy.energy SOS.eGenSet (elementaryRegular (H := H) k) x ≤ translationEnergy elementaryMoves k x := by
  classical
  have hs : SOSEnergy.energy SOS.eGenSet (elementaryRegular (H := H) k) x =
      ∑ g ∈ SOS.genSet, ‖leftTranslation (Congruence.Quotient k) (reduce k g) x - x‖ ^ 2 := by
    unfold SOSEnergy.energy
    apply Finset.sum_bij (fun (g : SOS.E) _ => (g : SOS.SL))
    · intro g hg
      exact SOS.mem_eGenSet.mp hg
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro g hg
      let e : SOS.E := ⟨g, Subgroup.subset_closure hg⟩
      exact ⟨e, SOS.mem_eGenSet.mpr hg, rfl⟩
    · intro g _
      rfl
  rw [hs]
  exact Finset.sum_le_sum_of_subset_of_nonneg certificateGenerators_subset (fun _ _ _ => sq_nonneg _)

theorem elementaryEnergy_gap (k : ℕ)
    (hsurj : Function.Surjective (elementaryReduction k))
    (x : lp (fun _ : Congruence.Quotient k => H) 2)
    (hx : constantProjection (Congruence.Quotient k) x = 0) :
    (1 / 10 : ℝ) * ‖x‖ ^ 2 ≤ translationEnergy elementaryMoves k x := by
  have ho : x ∈ (elementaryLaplacian (H := H) k).kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    exact inner_eq_zero_of_projection_zero _ x y hx (elementaryKernel_projection_ca k hsurj y hy)
  exact (SOS.ElementarySpectral.deltaOp_gap (elementaryRegular (H := H) k) x ho).trans (elementaryEnergy_le k x)

/-- The required published gap follows from the integral certificate and
surjectivity onto the specified finite quotients. -/
theorem publishedKazhdanInput_of_elementaryReduction_ca_oai
    (hsurj : ∀ k, Function.Surjective (elementaryReduction k)) : PublishedKazhdanInput := by
  apply uniformAveragingGap_of_energy elementaryMoves elementaryMoves_nonempty (1 / 10)
    (by norm_num)
  · have hc : (1 : ℝ) ≤ elementaryMoves.card := by
      exact_mod_cast elementaryMoves_nonempty.card_pos
    linarith
  · intro k x hx
    exact elementaryEnergy_gap k (hsurj k) x hx

end CoarseAssembly

end

end OAI
end

theorem solution : type_of% @OAI.CoarseAssembly.publishedKazhdanInput_of_elementaryReduction_ca_oai := @OAI.CoarseAssembly.publishedKazhdanInput_of_elementaryReduction_ca_oai
