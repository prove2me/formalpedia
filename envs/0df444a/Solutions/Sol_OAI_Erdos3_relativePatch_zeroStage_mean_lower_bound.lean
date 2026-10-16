-- Prove2me | solution 1 for OAI.Erdos3.relativePatch_zeroStage_mean_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T04:34:25.123983+00:00
-- url     : https://prove2.me/submissions/d732d620-3428-4706-bde5-271e2f18a68b

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1324
import Definitions.Def_OAIErdos3B1380

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots


end PolynomialSlots

namespace PolynomialPatch


end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots


end PolynomialSlots

namespace PolynomialPatch


end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

theorem value_rank_zero (A : PolynomialPatch σ s 0) (t : σ → ℝ) :
    A.value t = A.kernel.value 0 := by
  have h := (A.form.slots t).patchValue_eq_at_residual A.kernel
    (b := 0) (fun i => Fin.elim0 i)
  have hr : (A.form.slots t).residual 0 = 0 := Subsingleton.elim _ _
  simpa only [value, hr] using h

end PolynomialPatch

namespace PolynomialPatch

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots


end PolynomialSlots

namespace PolynomialPatch


end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open _root_.MvPolynomial


end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots


end PolynomialSlots

end Erdos3

end

section

namespace Erdos3

namespace PolynomialPatch


end PolynomialPatch

end Erdos3

end

section

namespace Erdos3
namespace PolynomialPatch

open _root_.MvPolynomial


end PolynomialPatch
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem relativePatchDistinctWeights_eq_zero_iff {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) : relativePatchDistinctWeights A = 0 ↔ d = 0 := by
  constructor
  · intro h
    by_contra hd
    let i : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
    have hm : A.weight i ∈ Finset.univ.image A.weight :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have he : Finset.univ.image A.weight = ∅ := Finset.card_eq_zero.mp h
    simp only [he, Finset.notMem_empty] at hm
  · rintro rfl
    simp [relativePatchDistinctWeights]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

namespace ResidueBoxSlice


end ResidueBoxSlice

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice


end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice


end ResidueBoxSlice

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators Classical

attribute [local irreducible] selectedJointReference selectedResidueFiniteLaw

theorem zero_slot_score_mean_lower_bound {X : Type*} [Fintype X] [DecidableEq X]
    {s : ℕ} (B : PolynomialPatch X s 0) (N : X → ℕ)
    (hN : (integerBox N).Nonempty) (f : (X → ℤ) → ℝ) {a σ : ℝ}
    (hσ : 0 < σ)
    (hscore : σ ≤ 𝔼 x ∈ integerBox N,
      (f x - a) * B.value (fun i => (x i : ℝ))) :
    a + σ ≤ 𝔼 x ∈ integerBox N, f x := by
  have hc := B.value_mem_Icc (fun _ => 0)
  simp only [PolynomialPatch.value_rank_zero] at hc hscore
  rw [← Finset.expect_mul, Finset.expect_sub_distrib, Finset.expect_const hN] at hscore
  have hpos : 0 ≤ (𝔼 x ∈ integerBox N, f x) - a := by
    by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hc.1
    linarith
  have hle := mul_le_mul_of_nonneg_left hc.2 hpos
  linarith

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativeBoxInput_expect {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ) :
    (𝔼 x ∈ integerBox N, relativeBoxInput N f x) = (𝔼 x ∈ integerBox N, f x) := by
  apply Finset.expect_congr rfl
  intro x hx
  exact relativeBoxInput_eq N f (by simpa using hx)

theorem relativePatch_zeroStage_mean_lower_bound_oai
    {X : Type*} [Fintype X] [DecidableEq X] {s d : ℕ}
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (f : (X → ℤ) → ℝ)
    (patch : PolynomialPatch X s d) {a surplus : ℝ}
    (hsurplus : 0 < surplus)
    (hstage : relativePatchDistinctWeights patch ≤ 0)
    (hscore : surplus ≤ relativePatchBoxScore N f a patch) :
    d = 0 ∧ a + surplus ≤ (𝔼 x ∈ integerBox N, relativeBoxInput N f x) := by
  have hd : d = 0 := (relativePatchDistinctWeights_eq_zero_iff patch).mp (Nat.eq_zero_of_le_zero hstage)
  refine ⟨hd, ?_⟩
  subst d
  rw [relativeBoxInput_expect]
  have hbox : (integerBox N).Nonempty := by
    refine ⟨fun _ => 0, (mem_integerBox N _).mpr ?_⟩
    intro i
    exact ⟨le_refl _, by exact_mod_cast hN i⟩
  exact zero_slot_score_mean_lower_bound patch N hbox f hsurplus hscore

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical




end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical




end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

open Module Submodule

end Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.relativePatch_zeroStage_mean_lower_bound_oai.{u_1} := @OAI.Erdos3.relativePatch_zeroStage_mean_lower_bound_oai.{u_1}
