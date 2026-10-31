-- Prove2me | solution 1 for HighDimStat.Rkhs.moore_aronszajn_existence_v2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T03:15:42.246983+00:00
-- url     : https://prove2.me/submissions/f6346021-e7c9-4919-8a97-c54489894c04

import Mathlib
import Definitions.Def_HighDimStat_Rkhs_Core

open ContinuousLinearMap
open scoped InnerProductSpace BigOperators RealInnerProductSpace

noncomputable section

namespace HighDimStat.Rkhs

variable {X : Type} (K : X → X → ℝ)

/-- The operator-valued kernel on `X` induced by `K`, where each entry is scalar multiplication. -/
def opK : Matrix X X (ℝ →L[ℝ] ℝ) :=
  Matrix.of fun x y => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (K x y)

lemma opK_isHermitian (hKsymm : ∀ x y, K x y = K y x) : (opK K).IsHermitian := by
  ext x y
  refine ext_inner_right ℝ fun w => ?_
  simp only [Matrix.conjTranspose_apply, star, adjoint_inner_left]
  simp [opK, ContinuousLinearMap.smulRight_apply, hKsymm x y]

lemma opK_apply_inner (hKsymm : ∀ x y, K x y = K y x) (x y : X) (u v : ℝ) :
    ⟪opK K y x u, v⟫_ℝ = u * v * K x y := by
  simp [opK, ContinuousLinearMap.smulRight_apply, hKsymm y x]
  ring

lemma double_sum_equiv (s : Finset X) (F : X → X → ℝ) :
    (∑ x ∈ s, ∑ y ∈ s, F x y) =
      ∑ i : Fin s.card, ∑ j : Fin s.card, F (s.equivFin.symm i).1 (s.equivFin.symm j).1 := by
  have h1 : (∑ x ∈ s, ∑ y ∈ s, F x y) = ∑ x : s, ∑ y ∈ s, F x.1 y := by
    rw [← Finset.sum_attach]
    rfl
  rw [h1, ← Equiv.sum_comp s.equivFin.symm (fun (x : s) => ∑ y ∈ s, F x.1 y)]
  apply Finset.sum_congr rfl
  intro i _
  have h2 : (∑ y ∈ s, F (s.equivFin.symm i).1 y) = ∑ y : s, F (s.equivFin.symm i).1 y.1 := by
    rw [← Finset.sum_attach]
    rfl
  rw [h2, ← Equiv.sum_comp s.equivFin.symm (fun (y : s) => F (s.equivFin.symm i).1 y.1)]

/-- `opK K` is positive semidefinite whenever `K` is a PSD kernel in the sense of Wainwright. -/
lemma opK_posSemidef (hK : IsPSDKernel K) : (opK K).PosSemidef := by
  have htfae := @RKHS.posSemidef_tfae ℝ _ X ℝ _ _ _ (opK K)
  apply (htfae.out 2 0).mp
  refine ⟨opK_isHermitian K hK.1, fun vv => ?_⟩
  change 0 ≤ vv.sum fun x w => vv.sum fun y w' => ⟪opK K y x w, w'⟫_ℝ
  simp only [Finsupp.sum, opK_apply_inner K hK.1]
  rw [double_sum_equiv vv.support (fun x y => vv x * vv y * K x y)]
  exact hK.2 (vv.support.card) (fun i => (vv.support.equivFin.symm i).1) (fun i => vv (vv.support.equivFin.symm i).1)

section RKHSBuild

variable [hpos : Fact (opK K).PosSemidef]

local notation "H" => RKHS.OfKernel (opK K)

def toFunCLM : H →ₗ[ℝ] (X → ℝ) :=
  (RKHS.coeCLM ℝ : H →L[ℝ] (X → ℝ)).toLinearMap

def feat (x : X) : H :=
  RKHS.kerFun H x (1 : ℝ)

lemma toFun_inj : Function.Injective (toFunCLM K) :=
  RKHS.coeCLM_injective

lemma feat_eq (x : X) : toFunCLM K (feat K x) = fun z => K z x := by
  ext z
  change (RKHS.kerFun H x 1) z = K z x
  rw [RKHS.kerFun_apply, RKHS.OfKernel.kernel_ofKernel]
  simp [opK]

lemma repr (f : H) (x : X) : ⟪f, feat K x⟫ = toFunCLM K f x := by
  change ⟪f, RKHS.kerFun H x 1⟫_ℝ = toFunCLM K f x
  rw [RKHS.inner_kerFun]
  change ⟪f x, (1 : ℝ)⟫_ℝ = f x
  simp

end RKHSBuild

/-- **Existence half of the Moore-Aronszajn theorem (Wainwright Theorem 12.11, p. 389).**
For any positive semidefinite kernel `K` on `X`, completing the pre-Hilbert space of finite linear
combinations of kernel sections `K(·, x)` yields a Hilbert space `H` with linear embedding `toFun`
and feature map `feature` satisfying `IsRKHS K toFun feature`. -/
theorem moore_aronszajn_existence_v2 {X : Type} (K : X → X → ℝ) (hK : IsPSDKernel K) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (toFun : H →ₗ[ℝ] (X → ℝ)) (feature : X → H), IsRKHS K toFun feature := by
  have : Fact (opK K).PosSemidef := ⟨opK_posSemidef K hK⟩
  let H : Type := RKHS.OfKernel (opK K)
  refine ⟨H, inferInstance, inferInstance, inferInstance, toFunCLM K, feat K, ?_⟩
  exact {
    toFun_injective := toFun_inj K
    feature_eq := feat_eq K
    reproducing := repr K
  }

abbrev solution := @moore_aronszajn_existence_v2

end HighDimStat.Rkhs

abbrev solution := @HighDimStat.Rkhs.moore_aronszajn_existence_v2
