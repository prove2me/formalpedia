-- Prove2me | solution 1 for OAI.KaplanskyConsequences.Regular.algebra_F2_simple
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:40:28.561694+00:00
-- url     : https://prove2.me/submissions/af58347f-18b8-44d5-b219-3008c3457d53

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf011
import Theorems.Thm_OAI_KaplanskyConsequences_Regular_polynomial_average_small
import Theorems.Thm_OAI_KaplanskyConsequences_Regular_polynomial_dense_zero

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_PowersOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance 2000] Classical.propDecidable Classical.decEq
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {G H : Type*} [Group G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

omit [CompleteSpace H] in
lemma left_norm_le (g : G) : ‖left (H:=H) g‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  exact le_of_eq ((reindex (Equiv.mulLeft g)).norm_map x |>.trans (one_mul _).symm)

lemma conjugate_norm_le (g : G) (T : HilbertSum G H →L[ℂ] HilbertSum G H) :
    ‖left g*T*left g⁻¹‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖left (H:=H) g‖ * ‖T‖ * ‖left (H:=H) g⁻¹‖ := norm_mul_le_of_le (norm_mul_le _ _) le_rfl
    _ ≤ 1 * ‖T‖ * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right (left_norm_le g) (norm_nonneg _)) (left_norm_le _)
      (norm_nonneg _) (by positivity)
    _ = _ := by ring


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_PowersAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance 2000] Classical.propDecidable Classical.decEq
variable {G : Type*} [Group G]

lemma conjugateMap_norm_le (g : G) (x : Algebra G) :
    ‖conjugateMap g x‖ ≤ ‖x‖ := conjugate_norm_le g x.val

lemma averageConjugate_apply {N : ℕ} (h : Fin N → G) (x : Algebra G) :
    averageConjugate h x = (N:ℂ)⁻¹ • ∑ i, conjugateMap (h i) x := by
  change (N:ℂ)⁻¹ • ((∑ i, conjugateMap (h i)) : Algebra G →ₗ[ℂ] Algebra G) x = _
  rw [LinearMap.sum_apply]

lemma averageConjugate_norm_le {N : ℕ} (hN : 0<N) (h : Fin N → G) (x : Algebra G) :
    ‖averageConjugate h x‖ ≤ ‖x‖ := by
  rw [averageConjugate_apply,norm_smul,norm_inv,Complex.norm_natCast]
  have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  calc
    _ ≤ (N:ℝ)⁻¹ * ∑ i, ‖conjugateMap (h i) x‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) (le_of_lt (inv_pos.mpr hn))
    _ ≤ (N:ℝ)⁻¹ * ∑ _i : Fin N, ‖x‖ := by gcongr with i; exact conjugateMap_norm_le _ _
    _ = ‖x‖ := by simp [nsmul_eq_mul,ne_of_gt hn]

@[simp] lemma averageConjugate_one {N : ℕ} (hN : 0<N) (h : Fin N → G) :
    averageConjugate h (1:Algebra G) = 1 := by
  rw [averageConjugate_apply]
  simp only [conjugateMap_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [←Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)),one_smul]


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_PowersAverageBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance 2000] Classical.propDecidable Classical.decEq
variable {G : Type*} [Group G]

lemma average_approximation_bound {N : ℕ} (hN : 0<N) (h : Fin N → G)
    (x y : Algebra G) : ‖averageConjugate h x‖ ≤ ‖x-y‖+‖averageConjugate h y‖ := by
  have hax := averageConjugate_norm_le hN h (x-y)
  have hab := norm_add_le (averageConjugate h (x-y)) (averageConjugate h y)
  rw [map_sub,sub_add_cancel] at hab
  rw [map_sub] at hax
  linarith


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_ReducedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped InnerProductSpace ComplexOrder BigOperators ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance 2200] Complex.partialOrder
variable {G : Type*}

variable [Group G]

lemma delta_cyclic (T : Algebra G) (h : T.val (delta 1) = 0) : T = 0 := by
  have hd (g : G) : T.val (delta g) = 0 := by
    ext k
    rw [algebra_delta,h]; rfl
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  change T.val x = 0
  have hs := (T.val.hasSum (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) x))
  have hz (g : G) : T.val (lp.single 2 g (x g)) = 0 := by
    have he : lp.single 2 g (x g) = (x g) • delta g := by
      ext k
      by_cases hkg : k=g <;> simp [delta_apply,lp.single_apply,hkg]
    rw [he,map_smul,hd,smul_zero]
  simp only [hz] at hs
  exact hs.unique hasSum_zero

lemma coefficient_faithful (T : Algebra G) (h : coefficient (star T*T) = 0) : T=0 := by
  rw [coefficient_square] at h
  exact delta_cyclic T ((inner_self_eq_zero).mp h)


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_PowersAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal

theorem powers_averaging (x : Algebra F2) (hx : coefficient x=0) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, 0<N ∧ ∃ h : Fin N → F2, ‖averageConjugate h x‖ < ε := by
  obtain ⟨c,hc,hxc⟩ := polynomial_dense_zero x hx (ε/2) (half_pos hε)
  obtain ⟨N,hN,h,hh⟩ := polynomial_average_small c hc (ε/2) (half_pos hε)
  refine ⟨N,hN,h,?_⟩
  exact lt_of_le_of_lt (average_approximation_bound hN h x (polynomial c))
    (by linarith)


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_PowersSimple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal ComplexOrder

lemma conjugateMap_mem_ideal (I : ClosedStarIdeal (Algebra F2)) (g : F2)
    {x : Algebra F2} (hx : x ∈ I.toNonUnitalStarSubalgebra) :
    conjugateMap g x ∈ I.toNonUnitalStarSubalgebra :=
  I.mul_mem_right _ _ (I.mul_mem_left _ _ hx)

lemma averageConjugate_mem_ideal (I : ClosedStarIdeal (Algebra F2)) {N : ℕ}
    (h : Fin N → F2) {x : Algebra F2} (hx : x ∈ I.toNonUnitalStarSubalgebra) :
    averageConjugate h x ∈ I.toNonUnitalStarSubalgebra := by
  rw [averageConjugate_apply]
  exact I.toNonUnitalStarSubalgebra.smul_mem _ (I.toNonUnitalStarSubalgebra.sum_mem
    (fun i hi => conjugateMap_mem_ideal I (h i) hx))

theorem algebra_F2_simple_oai : CStarSimple (Algebra F2) := by
  intro I
  by_cases hI : ∀ a : Algebra F2, a ∈ I.toNonUnitalStarSubalgebra → a=0
  · exact Or.inl hI
  · right
    push Not at hI
    obtain ⟨a,ha,hane⟩ := hI
    have ht : coefficient (star a*a) ≠ 0 := fun h => hane (coefficient_faithful a h)
    let b : Algebra F2 := (coefficient (star a*a))⁻¹ • (star a*a)
    have hb : coefficient b = 1 := by
      change canonicalTrace.functional ((coefficient (star a*a))⁻¹ • (star a*a))=1
      rw [map_smul]
      change (coefficient (star a*a))⁻¹ * coefficient (star a*a)=1
      exact inv_mul_cancel₀ ht
    have hbI : b ∈ I.toNonUnitalStarSubalgebra :=
      I.toNonUnitalStarSubalgebra.smul_mem _ (I.mul_mem_left _ _ ha)
    have hzero : coefficient (b-1)=0 := by
      change canonicalTrace.functional (b-1)=0
      rw [map_sub,canonicalTrace.normalized]
      change coefficient b - 1 = 0
      rw [hb,sub_self]
    obtain ⟨N,hN,h,hh⟩ := powers_averaging (b-1) hzero 1 zero_lt_one
    rw [map_sub,averageConjugate_one hN] at hh
    have hu : IsUnit (averageConjugate h b) := by
      have he : ‖1-averageConjugate h b‖<1 := by simpa only [norm_sub_rev] using hh
      simpa only [Units.val_oneSub,sub_sub_self] using (Units.oneSub (1-averageConjugate h b) he).isUnit
    obtain ⟨u,hu⟩ := hu
    have hunit : (u : Algebra F2) ∈ I.toNonUnitalStarSubalgebra := by
      rw [hu]
      exact averageConjugate_mem_ideal I h hbI
    have hone : (1 : Algebra F2) ∈ I.toNonUnitalStarSubalgebra := by
      simpa only [Units.inv_mul] using I.mul_mem_left (↑u⁻¹) u hunit
    intro x
    simpa only [mul_one] using I.mul_mem_left x 1 hone


end KaplanskyConsequences.Regular

end

end OAI
end

theorem solution : type_of% @OAI.KaplanskyConsequences.Regular.algebra_F2_simple_oai := @OAI.KaplanskyConsequences.Regular.algebra_F2_simple_oai
