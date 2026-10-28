-- Prove2me | solution 1 for OAI.Heisenberg.finite_cube_gibbs_strip
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T08:46:47.45599+00:00
-- url     : https://prove2.me/submissions/f6e911dd-2750-4bf9-82ff-b6ed13f63c30

import Mathlib
import Definitions.Def_Heisenberg
import Definitions.Def_OAIW2HM002
import Theorems.Thm_OAI_Heisenberg_cubeBoundary_lower
import Theorems.Thm_OAI_Heisenberg_cubeBoundary_upper

section
-- module Solutions.OAIW2_Heis.Heisenberg_LocalAlgebra
attribute [-instance] _root_.OAI.Heisenberg.quasiLocalClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical

open scoped ComplexConjugate BigOperators
namespace Heisenberg

lemma localUnit_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d}
    (hx : x ∈ F) (a b : Level ℓ) : localUnit d ℓ x a b ∈ localAlgebra d ℓ F :=
  StarAlgebra.subset_adjoin ℂ _ ⟨x, hx, a, b, rfl⟩

lemma spinZ_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinZ d ℓ x ∈ localAlgebra d ℓ F := by
  apply Subalgebra.sum_mem
  intro k _
  exact (localAlgebra d ℓ F).smul_mem (localUnit_mem_localAlgebra d ℓ F hx k k) _

lemma spinPlus_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinPlus d ℓ x ∈ localAlgebra d ℓ F := by
  apply Subalgebra.sum_mem
  intro k _
  exact (localAlgebra d ℓ F).smul_mem (localUnit_mem_localAlgebra d ℓ F hx k.succ k.castSucc) _

lemma spinMinus_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinMinus d ℓ x ∈ localAlgebra d ℓ F :=
  star_mem (spinPlus_mem_localAlgebra d ℓ F hx)

lemma spinX_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinX d ℓ x ∈ localAlgebra d ℓ F :=
  (localAlgebra d ℓ F).smul_mem ((localAlgebra d ℓ F).add_mem
    (spinPlus_mem_localAlgebra d ℓ F hx) (spinMinus_mem_localAlgebra d ℓ F hx)) _

lemma spinY_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinY d ℓ x ∈ localAlgebra d ℓ F :=
  (localAlgebra d ℓ F).smul_mem ((localAlgebra d ℓ F).sub_mem
    (spinPlus_mem_localAlgebra d ℓ F hx) (spinMinus_mem_localAlgebra d ℓ F hx)) _

theorem localAlgebras_commute {d ℓ : ℕ} {F G : Set (Site d)} (hFG : Disjoint F G)
    {A B : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ F) (hB : B ∈ localAlgebra d ℓ G) :
    Commute A B := by
  have hg (x : Site d) (hx : x ∈ F) (a b : Level ℓ) :
      localAlgebra d ℓ G ≤ StarSubalgebra.centralizer ℂ {localUnit d ℓ x a b} := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨y, hy, c, e, rfl⟩
    have hxy : x ≠ y := fun h => (Set.disjoint_left.mp hFG hx) (h ▸ hy)
    change _ ∈ StarSubalgebra.centralizer ℂ _
    rw [StarSubalgebra.mem_centralizer_iff ℂ]
    rintro _ rfl
    exact ⟨(localUnits_commute hxy a b c e).eq, by
      rw [star_localUnit]
      exact (localUnits_commute hxy b a c e).eq⟩
  have hle : localAlgebra d ℓ F ≤ StarSubalgebra.centralizer ℂ {B} := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨x, hx, a, b, rfl⟩
    have h₁ := ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hg x hx a b hB)) _ (Set.mem_singleton _)
    have h₂ := ((StarSubalgebra.mem_centralizer_iff ℂ).mp
      (hg x hx a b (star_mem hB))) _ (Set.mem_singleton _)
    change _ ∈ StarSubalgebra.centralizer ℂ _
    rw [StarSubalgebra.mem_centralizer_iff ℂ]
    rintro _ rfl
    exact ⟨h₁.1.symm, h₂.1.symm⟩
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle hA)) B (Set.mem_singleton B)).1.symm

lemma singleton_local_commute {d ℓ : ℕ} {x y : Site d} (hxy : x ≠ y)
    {A B : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ {x})
    (hB : B ∈ localAlgebra d ℓ {y}) : Commute A B :=
  localAlgebras_commute (Set.disjoint_singleton.mpr hxy) hA hB

lemma nearestNeighbor_ne {d : ℕ} {x y : Site d} (h : NearestNeighbor x y) : x ≠ y := by
  intro he
  subst y
  simp [NearestNeighbor] at h

theorem star_hamiltonian (d ℓ : ℕ) (Λ : Finset (Site d)) :
    star (hamiltonian d ℓ Λ) = hamiltonian d ℓ Λ := by
  classical
  simp only [hamiltonian, star_neg, star_sum, star_add, star_mul,
    star_spinX, star_spinY, star_spinZ]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  have hxy := nearestNeighbor_ne (Finset.mem_filter.mp he).2.1
  have hX := singleton_local_commute hxy (spinX_mem_localAlgebra d ℓ {e.1} rfl)
    (spinX_mem_localAlgebra d ℓ {e.2} rfl)
  have hY := singleton_local_commute hxy (spinY_mem_localAlgebra d ℓ {e.1} rfl)
    (spinY_mem_localAlgebra d ℓ {e.2} rfl)
  have hZ := singleton_local_commute hxy (spinZ_mem_localAlgebra d ℓ {e.1} rfl)
    (spinZ_mem_localAlgebra d ℓ {e.2} rfl)
  rw [hX.eq, hY.eq, hZ.eq]

lemma hamiltonian_selfAdjoint (d ℓ : ℕ) (Λ : Finset (Site d)) :
    IsSelfAdjoint (hamiltonian d ℓ Λ) := star_hamiltonian d ℓ Λ

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_StateCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators
open Filter Topology Metric
open scoped NNReal
open scoped NNReal

namespace Heisenberg

open scoped ComplexOrder

theorem positive_norm_bound {E : Type*} [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] (φ : E →L[ℂ] ℂ) (hn : φ 1 = 1)
    (hpos : ∀ B, 0 ≤ φ (star B * B)) : ‖φ‖ ≤ 4 := by
  have hp : ∀ A : E, 0 ≤ A → 0 ≤ φ A := by
    intro A hA
    obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
    exact hpos B
  let f : E →ₚ[ℂ] ℂ :=
    { φ.toLinearMap with
      monotone' := by
        intro A B h
        change φ A ≤ φ B
        have h' := hp (B - A) (sub_nonneg.mpr h)
        simpa only [map_sub, sub_nonneg] using h' }
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro A
  obtain ⟨x, hx, hnorm, hA⟩ := CStarAlgebra.exists_sum_four_nonneg A
  conv_lhs => rw [hA, map_sum]
  calc
    ‖∑ i : Fin 4, φ (Complex.I ^ (i : ℕ) • x i)‖ ≤
        ∑ i : Fin 4, ‖φ (Complex.I ^ (i : ℕ) • x i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul, norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
      have hi := PositiveLinearMap.norm_apply_le_of_nonneg f (x i) (hx i)
      change ‖φ (x i)‖ ≤ ‖φ 1‖ * ‖x i‖ at hi
      simpa only [hn, norm_one, one_mul] using hi.trans
        (by simpa only [hn, norm_one, one_mul] using hnorm i)
    _ = 4 * ‖A‖ := by simp

theorem state_norm_bound {d ℓ : ℕ} (ω : State d ℓ) : ‖ω.functional‖ ≤ 4 := by
  let : PartialOrder (QuasiLocal d ℓ) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (QuasiLocal d ℓ) := CStarAlgebra.spectralOrderedRing _
  exact positive_norm_bound ω.functional ω.normalized
    (fun B => ⟨(ω.positive B).2, by simpa using (ω.positive B).1.symm⟩)

open scoped InnerProductSpace

lemma star_gibbsHalf {d ℓ : ℕ} {K : QuasiLocal d ℓ} (hK : IsSelfAdjoint K) (β : ℝ) :
    star (gibbsHalf K β) = gibbsHalf K β := by
  rw [gibbsHalf, NormedSpace.star_exp, star_smul, hK]
  simp

lemma gibbsHalf_sq {d ℓ : ℕ} (K : QuasiLocal d ℓ) (β : ℝ) :
    gibbsHalf K β * gibbsHalf K β = gibbsDensity K β := by
  unfold gibbsHalf gibbsDensity
  rw [← NormedSpace.exp_add_of_commute (Commute.refl _), ← add_smul]
  congr 2
  push_cast
  ring

theorem gibbsState_apply {d ℓ : ℕ} (τ : State d ℓ)
    (hτ : ∀ A B, τ.functional (A*B) = τ.functional (B*A))
    {K : QuasiLocal d ℓ} (hK : IsSelfAdjoint K) (β : ℝ) (A : QuasiLocal d ℓ) :
    (gibbsState τ K β).functional A =
      ((τ.functional (gibbsDensity K β)).re : ℂ)⁻¹ *
        τ.functional (gibbsDensity K β * A) := by
  change ((sandwichFunctional τ.functional (gibbsHalf K β) 1).re : ℂ)⁻¹ *
    sandwichFunctional τ.functional (gibbsHalf K β) A = _
  simp only [sandwichFunctional_apply, mul_one, star_gibbsHalf hK, gibbsHalf_sq]
  congr 1
  rw [hτ (_*A), ← mul_assoc, gibbsHalf_sq]

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_BoundedStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators
open Filter Topology Metric
open scoped NNReal
open scoped NNReal

open scoped ComplexConjugate Topology
namespace GibbsStrip
variable {E : Type*} [CStarAlgebra E]

attribute [local instance] OAI.GibbsStrip.instNormedAlgebraRat_solutions
lemma exp_scalar_add (K : E) (z w : ℂ) :
    NormedSpace.exp ((z+w) • K) = NormedSpace.exp (z • K) * NormedSpace.exp (w • K) := by
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute ((Commute.refl K).smul_left z |>.smul_right w)

lemma evolve_add (K : E) (z w : ℂ) (A : E) :
    evolve K (z+w) A = evolve K z (evolve K w A) := by
  unfold evolve
  rw [mul_add,exp_scalar_add]
  have he : -(Complex.I*z+Complex.I*w) = -(Complex.I*w) + -(Complex.I*z) := by ring
  rw [he,exp_scalar_add]
  simp only [mul_assoc]

lemma evolve_differentiable (K A : E) : Differentiable ℂ (fun z => evolve K z A) := by
  have h (c : ℂ) : Differentiable ℂ (fun z : ℂ => NormedSpace.exp ((c*z) • K)) := by
    have hh : Differentiable ℂ (fun z : ℂ => NormedSpace.exp (z • K)) :=
      fun z => (hasDerivAt_exp_smul_const K z).differentiableAt
    exact hh.comp ((differentiable_const c).mul differentiable_id)
  unfold evolve
  have hh := ((h Complex.I).mul_const A).mul (h (-Complex.I))
  change Differentiable ℂ (fun z => NormedSpace.exp ((Complex.I*z) • K) * A *
    NormedSpace.exp (((-Complex.I)*z) • K)) at hh
  simpa only [neg_mul] using hh

lemma real_evolve_norm {K : E} (hK : IsSelfAdjoint K) (t : ℝ) (A : E) :
    ‖evolve K (t : ℂ) A‖ = ‖A‖ := by
  have h (t : ℝ) : NormedSpace.exp ((Complex.I*(t:ℂ)) • K) ∈ unitary E := by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    apply IsSelfAdjoint.smul_mem_skewAdjoint _ hK
    change star (Complex.I*(t:ℂ)) = -(Complex.I*(t:ℂ))
    simp
  have hn : NormedSpace.exp ((-(Complex.I*(t:ℂ))) • K) ∈ unitary E := by
    convert h (-t) using 1; simp
  rw [evolve,CStarRing.norm_mul_mem_unitary _ hn,CStarRing.norm_mem_unitary_mul _ (h t)]

lemma imaginary_evolve (K : E) (β : ℝ) (A : E) :
    evolve K (Complex.I * β) A =
      NormedSpace.exp ((-β : ℂ) • K) * A * NormedSpace.exp ((β : ℂ) • K) := by
  simp [evolve,← mul_assoc]

lemma exp_cancel_left (K : E) (z : ℂ) :
    NormedSpace.exp (z • K) * NormedSpace.exp ((-z) • K) = 1 := by
  rw [← exp_scalar_add]
  simp

lemma gibbs_upper_boundary (τ : E →L[ℂ] ℂ)
    (hτ : ∀ A B, τ (A*B) = τ (B*A)) (K : E) (β t : ℝ) (c : ℂ) (A B : E) :
    c * τ (NormedSpace.exp ((-β : ℂ) • K) * (A * evolve K ((t:ℂ)+Complex.I*β) B)) =
      c * τ (NormedSpace.exp ((-β : ℂ) • K) * (evolve K (t:ℂ) B * A)) := by
  rw [add_comm (t:ℂ),evolve_add,imaginary_evolve]
  congr 1
  let D := NormedSpace.exp ((-β : ℂ) • K)
  let D' := NormedSpace.exp ((β : ℂ) • K)
  let X := evolve K (t:ℂ) B
  change τ (D*(A*(D*X*D'))) = τ (D*(X*A))
  calc
    _ = τ ((D*(A*(D*X)))*D') := by simp only [mul_assoc]
    _ = τ (D'*(D*(A*(D*X)))) := hτ _ _
    _ = τ (A*(D*X)) := by
      rw [← mul_assoc D' D,show D'*D = 1 from exp_cancel_left K (β:ℂ),one_mul]
    _ = τ ((D*X)*A) := hτ _ _
    _ = _ := by rw [mul_assoc]

lemma strip_evolve_bounded {K : E} (hK : IsSelfAdjoint K) (A : E) (β : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, 0 ≤ z.im → z.im ≤ β → ‖evolve K z A‖ ≤ M := by
  have hc : Continuous (fun u : ℝ => ‖evolve K (Complex.I*(u:ℂ)) A‖) :=
    ((evolve_differentiable K A).continuous.comp
      (continuous_const.mul Complex.continuous_ofReal)).norm
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image (hc.continuousOn (s:=Set.Icc 0 β))
  refine ⟨max M 0,le_max_right _ _,fun z hz0 hzβ => ?_⟩
  have hz : z = (z.re:ℂ)+Complex.I*(z.im:ℂ) := by
    apply Complex.ext <;> simp
  rw [hz,evolve_add,real_evolve_norm hK]
  exact (hM ⟨z.im,⟨hz0,hzβ⟩,rfl⟩).trans (le_max_left _ _)

end GibbsStrip

open Set Filter Complex
open scoped Topology

namespace HeisenbergStrip

theorem bounded_strip_max {β C : ℝ} (hβ : 0 < β) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (openStrip β))
    (hbounded : ∃ M : ℝ, ∀ z ∈ closedStrip β, ‖f z‖ ≤ M)
    (hzero : ∀ z : ℂ, z.im = 0 → ‖f z‖ ≤ C)
    (htop : ∀ z : ℂ, z.im = β → ‖f z‖ ≤ C)
    {z : ℂ} (hz : z ∈ closedStrip β) : ‖f z‖ ≤ C := by
  apply PhragmenLindelof.horizontal_strip hf ?_ hzero htop hz.1 hz.2
  refine ⟨0, by simpa using div_pos Real.pi_pos hβ, 0, ?_⟩
  obtain ⟨M, hM⟩ := hbounded
  apply Asymptotics.IsBigO.of_bound M
  simp only [Filter.eventually_inf_principal]
  exact Filter.Eventually.of_forall (fun w hw => by
    simpa using hM w ⟨hw.1.le, hw.2.le⟩)

end HeisenbergStrip
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_GibbsLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators
open Filter Topology Metric
open scoped NNReal
open scoped ComplexConjugate Topology
open Set Filter Complex
open scoped Topology

namespace Heisenberg

open GibbsStrip

lemma state_apply_norm_le {d ℓ : ℕ} (ω : State d ℓ) (A : QuasiLocal d ℓ) :
    ‖ω.functional A‖ ≤ 4 * ‖A‖ :=
  (ω.functional.le_opNorm A).trans (mul_le_mul_of_nonneg_right (state_norm_bound ω) (norm_nonneg A))

lemma state_product_norm_le {d ℓ : ℕ} (ω : State d ℓ) (A B : QuasiLocal d ℓ) :
    ‖ω.functional (A*B)‖ ≤ 4*‖A‖*‖B‖ := by
  exact (state_apply_norm_le ω _).trans (by nlinarith [norm_mul_le A B])

theorem finite_gibbs_strip {d ℓ : ℕ} (τ : State d ℓ)
    (hτ : ∀ A B, τ.functional (A*B) = τ.functional (B*A))
    {K : QuasiLocal d ℓ} (hK : IsSelfAdjoint K) {β : ℝ} (hβ : 0 < β)
    (A B : QuasiLocal d ℓ) :
    ∃ F : ℂ → ℂ,
      DiffContOnCl ℂ F (HeisenbergStrip.openStrip β) ∧
      (∀ z ∈ HeisenbergStrip.closedStrip β, ‖F z‖ ≤ 4*‖A‖*‖B‖) ∧
      (∀ t : ℝ, F t = (gibbsState τ K β).functional (A * evolve K t B)) ∧
      (∀ t : ℝ, F ((t:ℂ)+Complex.I*β) = (gibbsState τ K β).functional (evolve K t B * A)) := by
  let ω := gibbsState τ K β
  let F : ℂ → ℂ := fun z => ω.functional (A*evolve K z B)
  have hd : Differentiable ℂ F := ω.functional.differentiable.comp
    ((evolve_differentiable K B).const_mul A)
  have hu (t : ℝ) : F ((t:ℂ)+Complex.I*β) = ω.functional (evolve K t B*A) := by
    change (gibbsState τ K β).functional (A*evolve K ((t:ℂ)+Complex.I*β) B) =
      (gibbsState τ K β).functional (evolve K t B*A)
    rw [gibbsState_apply τ hτ hK,gibbsState_apply τ hτ hK]
    simpa only [gibbsDensity,Complex.ofReal_neg] using
      gibbs_upper_boundary τ.functional hτ K β t ((τ.functional (gibbsDensity K β)).re : ℂ)⁻¹ A B
  have hb : ∃ M : ℝ, ∀ z ∈ HeisenbergStrip.closedStrip β, ‖F z‖ ≤ M := by
    obtain ⟨M,hM0,hM⟩ := strip_evolve_bounded hK B β
    refine ⟨4*‖A‖*M, fun z hz => ?_⟩
    exact (state_product_norm_le ω A _).trans
      (mul_le_mul_of_nonneg_left (hM z hz.1 hz.2) (by positivity))
  refine ⟨F,hd.diffContOnCl,?_, fun _ => rfl,hu⟩
  intro z hz
  apply HeisenbergStrip.bounded_strip_max hβ hd.diffContOnCl hb ?_ ?_ hz
  · intro w hw
    have he : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hw]
    rw [he]
    exact (state_product_norm_le ω A _).trans_eq (by rw [real_evolve_norm hK])
  · intro w hw
    have he : w = (w.re:ℂ)+Complex.I*β := by apply Complex.ext <;> simp [hw]
    rw [he,hu]
    exact (state_product_norm_le ω _ A).trans_eq (by rw [real_evolve_norm hK]; ring)

open Filter Topology GibbsStrip

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg
open SlotTensor TensorMatrix
variable {d ℓ : ℕ}

lemma totalZ_selfAdjoint (Λ : Finset (Site d)) : IsSelfAdjoint (totalZ (ℓ:=ℓ) Λ) := by
  change star (totalZ Λ)=totalZ Λ
  simp only [totalZ,star_sum,star_spinZ]

lemma shiftedField_selfAdjoint (Λ : Finset (Site d)) (h : ℝ) :
    IsSelfAdjoint (shiftedField (ℓ:=ℓ) Λ h) := by
  change star (shiftedField Λ h)=shiftedField Λ h
  simp only [shiftedField,star_sub,star_add,star_smul,star_trivial,star_one,
    (hamiltonian_selfAdjoint d ℓ Λ).star_eq,(totalZ_selfAdjoint (ℓ:=ℓ) Λ).star_eq]

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg

variable {d ℓ : ℕ}

lemma diffContOnCl_sum {I : Type*} [Fintype I] {s : Set ℂ} (F : I → ℂ → ℂ)
    (hF : ∀ i,DiffContOnCl ℂ (F i) s) : DiffContOnCl ℂ (fun z=>∑ i,F i z) s := by
  constructor
  · convert DifferentiableOn.sum (u:=Finset.univ) (fun i _=>(hF i).1) using 1
    ext z
    simp only [Finset.sum_apply]
  · exact continuousOn_finsetSum _ (fun i _=>(hF i).2)

lemma norm_convex_sum {I : Type*} [Fintype I] (μ : I → ℝ) (hμ : ∀ i,0≤μ i)
    (hm : ∑ i,μ i=1) (f : I → ℂ) (C : ℝ) (hf : ∀ i,‖f i‖≤C) :
    ‖∑ i,(μ i:ℂ)*f i‖≤C := by
  calc _ ≤ ∑ i,‖(μ i:ℂ)*f i‖ := norm_sum_le _ _
       _ = ∑ i,μ i*‖f i‖ := by simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hμ _)]
       _ ≤ ∑ i,μ i*C := Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hf i) (hμ i))
       _ = C := by rw [←Finset.sum_mul,hm,one_mul]

theorem averaged_gibbs_strip {I : Type*} [Fintype I] (μ : I → ℝ) (hμ : ∀ i,0≤μ i)
    (hm : ∑ i,μ i=1) (x : I → Site d) (τ : State d ℓ)
    (hτ : ∀ A B,τ.functional (A*B)=τ.functional (B*A))
    (K : QuasiLocal d ℓ) (hK : IsSelfAdjoint K) {β : ℝ} (hβ : 0<β) (A B : QuasiLocal d ℓ) :
    ∃ F : ℂ → ℂ,DiffContOnCl ℂ F (HeisenbergStrip.openStrip β) ∧
      (∀ z ∈ HeisenbergStrip.closedStrip β,‖F z‖≤4*‖A‖*‖B‖) ∧
      (∀ t : ℝ,F t=∑ i,(μ i:ℂ)*(gibbsState τ K β).functional
        (translation d ℓ (x i) A*GibbsStrip.evolve K t (translation d ℓ (x i) B))) ∧
      (∀ t : ℝ,F ((t:ℂ)+Complex.I*β)=∑ i,(μ i:ℂ)*(gibbsState τ K β).functional
        (GibbsStrip.evolve K t (translation d ℓ (x i) B)*translation d ℓ (x i) A)) := by
  have hh (i : I):=finite_gibbs_strip τ hτ hK hβ (translation d ℓ (x i) A) (translation d ℓ (x i) B)
  choose F hd hb hzero htop using hh
  refine ⟨fun z=>∑ i,(μ i:ℂ)*F i z,?_,?_,?_,?_⟩
  · apply diffContOnCl_sum
    intro i
    exact ⟨(hd i).1.const_mul _,(hd i).2.const_mul _⟩
  · intro z hz
    apply norm_convex_sum μ hμ hm _ _
    intro i
    simpa only [norm_translation] using hb i z hz
  · intro t
    simp_rw [hzero]
  · intro t
    simp_rw [htop]

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinAveragedKMS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg
variable {d ℓ : ℕ}

lemma uniform_mass {X : Type*} (Λ : Finset X) (hΛ : Λ.Nonempty) :
    ∑ _ : Λ,(Λ.card:ℝ)⁻¹=1 := by
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
  exact mul_inv_cancel₀ (show (Λ.card:ℝ)≠0 by exact_mod_cast Finset.card_ne_zero.mpr hΛ)

lemma uniform_sum {X : Type*} (Λ : Finset X) (f : X → ℂ) :
    (∑ x : Λ,Complex.ofReal ((Λ.card:ℝ)⁻¹)*f x.val)=(Λ.card:ℂ)⁻¹*∑ x∈Λ,f x := by
  rw [←Finset.mul_sum,Finset.sum_coe_sort Λ f]
  simp only [Complex.ofReal_inv,Complex.ofReal_natCast]

lemma finite_cube_gibbs_strip_oai (Λ : Finset (Site d)) (hΛ : Λ.Nonempty) (h : ℝ)
    (τ : State d ℓ) (hτ : ∀ A B,τ.functional (A*B)=τ.functional (B*A))
    {β : ℝ} (hβ : 0<β) (A B : QuasiLocal d ℓ) :
    ∃ F : ℂ → ℂ,DiffContOnCl ℂ F (HeisenbergStrip.openStrip β) ∧
      (∀ z∈HeisenbergStrip.closedStrip β,‖F z‖≤4*‖A‖*‖B‖) ∧
      (∀ t : ℝ,F t=cubeBoundary Λ (gibbsState τ (shiftedField Λ h) β) h
        (ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ) A) B t) ∧
      (∀ t : ℝ,F ((t:ℂ)+Complex.I*β)=cubeBoundary Λ (gibbsState τ (shiftedField Λ h) β) h
        ((ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ)).flip A) B t) := by
  let μ : Λ → ℝ := fun _ => (Λ.card : ℝ)⁻¹
  have hμ : ∀ i, 0 ≤ μ i := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have hm : ∑ i, μ i = 1 := uniform_mass Λ hΛ
  have hh := averaged_gibbs_strip μ hμ hm (fun x : Λ => x.val) τ hτ
    (shiftedField Λ h) (shiftedField_selfAdjoint Λ h) hβ A B
  obtain ⟨F,hd,hb,h0,h1⟩ := hh
  refine ⟨F,hd,hb,?_,?_⟩
  · intro t
    exact (h0 t).trans ((uniform_sum Λ (fun x =>
      (gibbsState τ (shiftedField Λ h) β).functional
        (translation d ℓ x A * GibbsStrip.evolve (shiftedField Λ h) t (translation d ℓ x B)))).trans
      (cubeBoundary_lower Λ (gibbsState τ (shiftedField Λ h) β) h A B t).symm)
  · intro t
    exact (h1 t).trans ((uniform_sum Λ (fun x =>
      (gibbsState τ (shiftedField Λ h) β).functional
        (GibbsStrip.evolve (shiftedField Λ h) t (translation d ℓ x B) * translation d ℓ x A))).trans
      (cubeBoundary_upper Λ (gibbsState τ (shiftedField Λ h) β) h A B t).symm)

end Heisenberg
end
end

end OAI
end

theorem solution : type_of% @OAI.Heisenberg.finite_cube_gibbs_strip_oai := @OAI.Heisenberg.finite_cube_gibbs_strip_oai
