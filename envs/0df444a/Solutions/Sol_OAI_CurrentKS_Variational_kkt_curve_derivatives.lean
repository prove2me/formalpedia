-- Prove2me | solution 1 for OAI.CurrentKS.Variational.kkt_curve_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:58:37.186761+00:00
-- url     : https://prove2.me/submissions/a6eb4550-7b13-43b9-a6d5-a3eb60c7e702

import Mathlib
import Definitions.Def_OAIQ241TT006

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Calculus_NormMultilinearTwo
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Implicit
noncomputable section
open Filter
open scoped Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma norm_multilinear_two (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) G)
    (u v : E) : ‖B ![u,v]‖ ≤ ‖B‖*‖u‖*‖v‖ := by
  simpa only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,mul_assoc] using B.le_opNorm ![u,v]
lemma norm_multilinear_three (B : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) G)
    (u : E) : ‖B (fun _ => u)‖ ≤ ‖B‖*‖u‖^3 := by
  simpa using B.le_opNorm (fun _ => u)

lemma norm_implicit_inverse (J : F ≃L[ℝ] G) {A : ℝ} (hA : ‖J.symm.toContinuousLinearMap‖ ≤ A)
    (z : F) : ‖z‖ ≤ A*‖J z‖ := by
  calc
    ‖z‖ = ‖J.symm (J z)‖ := by rw [J.symm_apply_apply]
    _ ≤ ‖J.symm.toContinuousLinearMap‖*‖J z‖ := J.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)

theorem curve_bounds (funct : E → G) (c : ℝ → E) (a : ℝ)
    (hf : ContDiffAt ℝ 3 funct (c a)) (hc : ContDiffAt ℝ 3 c a)
    (heq : funct ∘ c =ᶠ[𝓝 a] fun _ => 0)
    (V : F →L[ℝ] E) (J : F ≃L[ℝ] G)
    (hJ : ∀ u, fderiv ℝ funct (c a) (V u) = J u)
    (v : E) (z₁ z₂ z₃ : F)
    (h₁ : deriv c a = v+V z₁) (h₂ : iteratedDeriv 2 c a = V z₂)
    (h₃ : iteratedDeriv 3 c a = V z₃)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hJinv : ‖J.symm.toContinuousLinearMap‖ ≤ A) (hV : ‖V‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hF₁ : ‖fderiv ℝ funct (c a)‖ ≤ D)
    (hF₂ : ‖iteratedFDeriv ℝ 2 funct (c a)‖ ≤ D)
    (hF₃ : ‖iteratedFDeriv ℝ 3 funct (c a)‖ ≤ D) :
    ‖z₁‖ ≤ A*D ∧ ‖z₂‖ ≤ A*D*(1+A*D)^2 ∧
      ‖z₃‖ ≤ A*D*((1+A*D)^3+3*(1+A*D)*(A*D*(1+A*D)^2)) := by
  have hzero (k : ℕ) (hk : k ≠ 0) : iteratedDeriv k (funct ∘ c) a = 0 := by
    rw [heq.iteratedDeriv_eq k,iteratedDeriv_const,ite_eq_right hk]
  have hfirst : fderiv ℝ funct (c a) (deriv c a) = 0 := by
    have h := (hf.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt a
      (hc.differentiableAt (by norm_num)).hasDerivAt
    rw [← h.deriv]
    simpa only [iteratedDeriv_one] using hzero 1 (by norm_num)
  have hJ₁ : J z₁ = -fderiv ℝ funct (c a) v := by
    rw [h₁,map_add,hJ] at hfirst
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hfirst)
  have hz₁ : ‖z₁‖ ≤ A*D := by
    calc
      _ ≤ A*‖J z₁‖ := norm_implicit_inverse J hJinv z₁
      _ = A*‖fderiv ℝ funct (c a) v‖ := by rw [hJ₁,norm_neg]
      _ ≤ A*(D*1) := mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.le_opNorm _ v).trans (mul_le_mul hF₁ hv (norm_nonneg _) hD)) hA
      _ = _ := by ring
  have hVnorm (u : F) : ‖V u‖ ≤ ‖u‖ :=
    (V.le_opNorm u).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hV (norm_nonneg u))
  have hc₁ : ‖deriv c a‖ ≤ 1+A*D := by
    rw [h₁]
    exact (norm_add_le _ _).trans (add_le_add hv ((hVnorm _).trans hz₁))
  have hU : 0 ≤ 1+A*D := by positivity
  have hs := iteratedDeriv_vcomp_two (hf.of_le (by norm_num)) (hc.of_le (by norm_num))
  rw [hzero 2 (by norm_num),h₂,hJ] at hs
  have hJ₂ : J z₂ = -iteratedFDeriv ℝ 2 funct (c a) (fun _ => deriv c a) := by
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hs.symm)
  have hz₂ : ‖z₂‖ ≤ A*D*(1+A*D)^2 := by
    calc
      _ ≤ A*‖J z₂‖ := norm_implicit_inverse J hJinv z₂
      _ = A*‖iteratedFDeriv ℝ 2 funct (c a) (fun _ => deriv c a)‖ := by rw [hJ₂,norm_neg]
      _ ≤ A*(D*(1+A*D)^2) := by
        apply mul_le_mul_of_nonneg_left _ hA
        calc
          _ ≤ ‖iteratedFDeriv ℝ 2 funct (c a)‖*‖deriv c a‖^2 := by
            simpa using (iteratedFDeriv ℝ 2 funct (c a)).le_opNorm (fun _ => deriv c a)
          _ ≤ _ := mul_le_mul hF₂ (pow_le_pow_left₀ (norm_nonneg _) hc₁ _) (sq_nonneg _) hD
      _ = _ := by ring
  have hc₂ : ‖iteratedDeriv 2 c a‖ ≤ A*D*(1+A*D)^2 := by
    rw [h₂]
    exact (hVnorm z₂).trans hz₂
  have hZ₂ : 0 ≤ A*D*(1+A*D)^2 := by positivity
  have ht := iteratedDeriv_vcomp_three hf hc
  rw [hzero 3 (by norm_num),h₃,hJ] at ht
  have hJ₃ : J z₃ = -(iteratedFDeriv ℝ 3 funct (c a) (fun _ => deriv c a)+
      iteratedFDeriv ℝ 2 funct (c a) ![iteratedDeriv 2 c a,deriv c a]+
      2 • iteratedFDeriv ℝ 2 funct (c a) ![deriv c a,iteratedDeriv 2 c a]) := by
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using ht.symm)
  have htriple : ‖iteratedFDeriv ℝ 3 funct (c a) (fun _ => deriv c a)‖ ≤ D*(1+A*D)^3 :=
    (norm_multilinear_three _ _).trans
      (mul_le_mul hF₃ (pow_le_pow_left₀ (norm_nonneg _) hc₁ _) (by positivity) hD)
  have hpair₁ : ‖iteratedFDeriv ℝ 2 funct (c a) ![iteratedDeriv 2 c a,deriv c a]‖ ≤ D*(A*D*(1+A*D)^2)*(1+A*D) :=
    (norm_multilinear_two _ _ _).trans
      (mul_le_mul (mul_le_mul hF₂ hc₂ (norm_nonneg _) hD) hc₁ (norm_nonneg _) (mul_nonneg hD hZ₂))
  have hpair₂ : ‖iteratedFDeriv ℝ 2 funct (c a) ![deriv c a,iteratedDeriv 2 c a]‖ ≤ D*(1+A*D)*(A*D*(1+A*D)^2) :=
    (norm_multilinear_two _ _ _).trans
      (mul_le_mul (mul_le_mul hF₂ hc₁ (norm_nonneg _) hD) hc₂ (norm_nonneg _) (mul_nonneg hD hU))
  refine ⟨hz₁,hz₂,?_⟩
  calc
    _ ≤ A*‖J z₃‖ := norm_implicit_inverse J hJinv z₃
    _ ≤ A*(D*(1+A*D)^3+D*(A*D*(1+A*D)^2)*(1+A*D)+2*(D*(1+A*D)*(A*D*(1+A*D)^2))) := by
      rw [hJ₃,norm_neg]
      apply mul_le_mul_of_nonneg_left _ hA
      calc
        _ ≤ ‖iteratedFDeriv ℝ 3 funct (c a) (fun _ => deriv c a)‖+
            ‖iteratedFDeriv ℝ 2 funct (c a) ![iteratedDeriv 2 c a,deriv c a]‖+
            ‖2 • iteratedFDeriv ℝ 2 funct (c a) ![deriv c a,iteratedDeriv 2 c a]‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
        _ ≤ _ := by
          exact add_le_add (add_le_add htriple hpair₁)
            (norm_nsmul_le.trans (by simpa using mul_le_mul_of_nonneg_left hpair₂ (by norm_num : (0 : ℝ) ≤ 2)))
    _ = _ := by ring

lemma iteratedDeriv_clm {c : ℝ → E} {a : ℝ} {n : ℕ} (hc : ContDiffAt ℝ n c a)
    (L : E →L[ℝ] G) : iteratedDeriv n (L ∘ c) a = L (iteratedDeriv n c a) := by
  rw [iteratedDeriv_eq_iteratedFDeriv,L.iteratedFDeriv_comp_left hc le_rfl]
  rfl

lemma iteratedDeriv_prod {f : ℝ → E} {g : ℝ → F} {a : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ n f a) (hg : ContDiffAt ℝ n g a) :
    iteratedDeriv n (fun t => (f t,g t)) a = (iteratedDeriv n f a,iteratedDeriv n g a) := by
  apply Prod.ext
  · have hh := iteratedDeriv_clm (hf.prodMk hg) (ContinuousLinearMap.fst ℝ E F)
    exact hh.symm
  · have hh := iteratedDeriv_clm (hf.prodMk hg) (ContinuousLinearMap.snd ℝ E F)
    exact hh.symm

lemma affine_deriv (x h : E) : deriv (fun t : ℝ => x+t • h) = fun _ => h := by
  funext t
  have hh := (((hasDerivAt_id t).smul_const h).const_add x).deriv
  simp only [one_smul] at hh
  exact hh
lemma affine_second (x h : E) (a : ℝ) : iteratedDeriv 2 (fun t : ℝ => x+t • h) a = 0 := by
  rw [show 2 = 1+1 from rfl,iteratedDeriv_succ',affine_deriv,iteratedDeriv_const]
  rfl
lemma affine_third (x h : E) (a : ℝ) : iteratedDeriv 3 (fun t : ℝ => x+t • h) a = 0 := by
  rw [show 3 = 2+1 from rfl,iteratedDeriv_succ',affine_deriv,iteratedDeriv_const]
  rfl

theorem graph_bounds (funct : E × F → G) (x h : E) (z : ℝ → F) (a : ℝ)
    (hf : ContDiffAt ℝ 3 funct (x+a • h,z a)) (hz : ContDiffAt ℝ 3 z a)
    (heq : (fun t => funct (x+t • h,z t)) =ᶠ[𝓝 a] fun _ => 0)
    (J : F ≃L[ℝ] G) (hJ : ∀ u, fderiv ℝ funct (x+a • h,z a) (0,u) = J u)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hJinv : ‖J.symm.toContinuousLinearMap‖ ≤ A) (hh : ‖h‖ ≤ 1)
    (hF₁ : ‖fderiv ℝ funct (x+a • h,z a)‖ ≤ D)
    (hF₂ : ‖iteratedFDeriv ℝ 2 funct (x+a • h,z a)‖ ≤ D)
    (hF₃ : ‖iteratedFDeriv ℝ 3 funct (x+a • h,z a)‖ ≤ D) :
    ‖deriv z a‖ ≤ A*D ∧ ‖iteratedDeriv 2 z a‖ ≤ A*D*(1+A*D)^2 ∧
      ‖iteratedDeriv 3 z a‖ ≤ A*D*((1+A*D)^3+3*(1+A*D)*(A*D*(1+A*D)^2)) := by
  have hl : ContDiff ℝ 3 (fun t : ℝ => x+t • h) := contDiff_const.add (contDiff_id.smul contDiff_const)
  have h₁ : deriv (fun t => (x+t • h,z t)) a = (h,0)+(ContinuousLinearMap.inr ℝ E F) (deriv z a) := by
    have hd := (((hasDerivAt_id a).smul_const h).const_add x).prodMk
      (hz.differentiableAt (by norm_num)).hasDerivAt
    simpa using hd.deriv
  have h₂ : iteratedDeriv 2 (fun t => (x+t • h,z t)) a = (ContinuousLinearMap.inr ℝ E F) (iteratedDeriv 2 z a) := by
    rw [iteratedDeriv_prod (hl.contDiffAt.of_le (by norm_num)) (hz.of_le (by norm_num)),affine_second]
    rfl
  have h₃ : iteratedDeriv 3 (fun t => (x+t • h,z t)) a = (ContinuousLinearMap.inr ℝ E F) (iteratedDeriv 3 z a) := by
    rw [iteratedDeriv_prod hl.contDiffAt hz,affine_third]
    rfl
  have hV : ‖ContinuousLinearMap.inr ℝ E F‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro u
    simp
  exact curve_bounds funct _ a hf (hl.contDiffAt.prodMk hz) heq (ContinuousLinearMap.inr ℝ E F) J hJ
    (h,0) (deriv z a) (iteratedDeriv 2 z a) (iteratedDeriv 3 z a) h₁ h₂ h₃ hA hD hJinv hV
    (by simpa using hh) hF₁ hF₂ hF₃

end
end CurrentKS.Implicit

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_JordanCLM
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p4
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r9969c5_1 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p4
lemma jordanCLM_val (A B U : H d) :
    ((jordanCLM A B U : H d) : Mat d) =
      (A : Mat d) * (U : Mat d) * (B : Mat d) + (B : Mat d) * (U : Mat d) * (A : Mat d) := by
  change ((A : Mat d)+(B : Mat d)) * (U : Mat d) * ((A : Mat d)+(B : Mat d)) -
    (A : Mat d)*(U : Mat d)*(A : Mat d) - (B : Mat d)*(U : Mat d)*(B : Mat d) = _
  noncomm_ring

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RetractH
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupMat_p2
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealMat_p2
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceMat_p2
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p6
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealSubtypeMatMemSubmoduleH_p6
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p6
lemma invH_retract (A : H d) : invH A = retractH (Ring.inverse (A : Mat d)) := by
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  exact (retractH_coe (invH A)).symm

lemma contDiffAt_invH {A : H d} (hA : A ∈ pd d) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n invH A := by
  obtain ⟨a,ha⟩ := hA.isUnit
  have hi : ContDiffAt ℝ n Ring.inverse (A : Mat d) := by
    rw [← ha]
    exact contDiffAt_ringInverse ℝ a
  have hc := (retractH (d := d)).contDiff.contDiffAt.comp A
    (hi.comp A (hermitianSubmodule d).subtypeL.contDiff.contDiffAt)
  apply hc.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun B => invH_retract B

lemma hasFDerivAt_invH {A : H d} (hA : A ∈ pd d) :
    HasFDerivAt invH (-sandwichCLM (invH A)) A := by
  obtain ⟨a,ha⟩ := hA.isUnit
  have hi : HasFDerivAt (fun B : Mat d => B⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (Mat d) (A : Mat d)⁻¹ (A : Mat d)⁻¹) (A : Mat d) := by
    rw [← ha]
    simpa only [Matrix.nonsing_inv_eq_ringInverse, Matrix.coe_units_inv] using
      (hasFDerivAt_ringInverse (𝕜 := ℝ) a)
  have hc := (retractH (d := d)).hasFDerivAt.comp A
    (hi.comp A (hermitianSubmodule d).subtypeL.hasFDerivAt)
  have he : (fun B : H d => retractH ((B : Mat d)⁻¹)) = invH := by
    funext B
    exact retractH_coe (invH B)
  change HasFDerivAt (fun B : H d => retractH ((B : Mat d)⁻¹)) _ A at hc
  rw [he] at hc
  refine hc.congr_fderiv ?_
  symm
  apply ContinuousLinearMap.ext
  intro U
  change -sandwich (invH A) U = retractH (-((A : Mat d)⁻¹ * (U : Mat d) * (A : Mat d)⁻¹))
  rw [map_neg]
  exact congrArg Neg.neg (retractH_coe (sandwich (invH A) U)).symm

lemma contDiff_sandwich {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun z : H d × H d => sandwich z.1 z.2) := by
  have hf : (fun z : H d × H d => sandwich z.1 z.2) =
      (fun z : H d × H d => retractH ((z.1 : Mat d) * (z.2 : Mat d) * (z.1 : Mat d))) := by
    funext z
    exact (retractH_coe (sandwich z.1 z.2)).symm
  rw [hf]
  apply (retractH (d := d)).contDiff.comp
  exact (((hermitianSubmodule d).subtypeL.contDiff.comp contDiff_fst).mul
    ((hermitianSubmodule d).subtypeL.contDiff.comp contDiff_snd)).mul
      ((hermitianSubmodule d).subtypeL.contDiff.comp contDiff_fst)

lemma hasFDerivAt_invSandwich (A P : H d) (hA : A ∈ pd d) :
    HasFDerivAt (fun z : H d × H d => sandwich (invH z.1) z.2)
      ((-jordanCLM (invH A) (sandwich (invH A) P)).comp (ContinuousLinearMap.fst ℝ (H d) (H d)) +
       (sandwichCLM (invH A)).comp (ContinuousLinearMap.snd ℝ (H d) (H d))) (A,P) := by
  let val := (hermitianSubmodule d).subtypeL
  have hInv := val.hasFDerivAt.comp (A,P)
    ((hasFDerivAt_invH hA).comp (A,P) (hasFDerivAt_fst (p := (A,P))))
  have hMid := val.hasFDerivAt.comp (A,P) (hasFDerivAt_snd (p := (A,P)))
  have hm := (hInv.mul' hMid).mul' hInv
  have hh := (retractH (d := d)).hasFDerivAt.comp (A,P) hm
  have he : (fun z : H d × H d => retractH
      (((invH z.1 : H d) : Mat d) * (z.2 : Mat d) * ((invH z.1 : H d) : Mat d))) =
      (fun z : H d × H d => sandwich (invH z.1) z.2) := by
    funext z
    exact retractH_coe (sandwich (invH z.1) z.2)
  change HasFDerivAt (fun z : H d × H d => retractH
    (((invH z.1 : H d) : Mat d) * (z.2 : Mat d) * ((invH z.1 : H d) : Mat d))) _ (A,P) at hh
  rw [he] at hh
  refine hh.congr_fderiv ?_
  symm
  apply ContinuousLinearMap.ext
  intro z
  change -jordanCLM (invH A) (sandwich (invH A) P) z.1 + sandwich (invH A) z.2 =
    retractH
      (((invH A : H d) : Mat d) * (P : Mat d) *
          (-(((invH A : H d) : Mat d) * (z.1 : Mat d) * ((invH A : H d) : Mat d))) +
       (((invH A : H d) : Mat d) * (z.2 : Mat d) +
          (-(((invH A : H d) : Mat d) * (z.1 : Mat d) * ((invH A : H d) : Mat d))) * (P : Mat d)) *
        ((invH A : H d) : Mat d))
  rw [← retractH_coe (-jordanCLM (invH A) (sandwich (invH A) P) z.1 + sandwich (invH A) z.2)]
  congr 1
  simp only [Submodule.coe_add, Submodule.coe_neg, jordanCLM_val, sandwich_val]
  noncomm_ring

lemma contDiffAt_invSandwich (A P : H d) (hA : A ∈ pd d) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun z : H d × H d => sandwich (invH z.1) z.2) (A,P) := by
  have hi : ContDiffAt ℝ n (fun z : H d × H d => invH z.1) (A,P) :=
    (contDiffAt_invH (d := d) (A := A) (n := n) hA).fst' (y := P)
  have hp : ContDiffAt ℝ n (fun z : H d × H d => (invH z.1, z.2)) (A,P) :=
    hi.prodMk (contDiffAt_snd (𝕜 := ℝ) (n := n) (p := (A,P)))
  have hs : ContDiffAt ℝ n (fun u : H d × H d => sandwich u.1 u.2) (invH A,P) :=
    (contDiff_sandwich (d := d) (n := n)).contDiffAt
  exact hs.comp (A,P) hp

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_FDerivTightPart
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d : ℕ}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p1
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealSubtypeMatMemSubmoduleH_p1
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1
lemma hasFDerivAt_tightPart (t : E →L[ℝ] ℝ) (X Y : E →L[ℝ] H d)
    (S : H d) (η : H d →L[ℝ] H d) (z : E) (hX : X z ∈ pd d) :
    HasFDerivAt (fun v => t v • (one : H d) - invH (X v) - S - η (Y v))
      ((t.smulRight (one : H d) : E →L[ℝ] H d) +
        ((sandwichCLM (invH (X z))).comp X : E →L[ℝ] H d) - η.comp Y) z := by
  have h := (((t.hasFDerivAt.smul_const (one : H d)).sub
    ((hasFDerivAt_invH hX).comp z X.hasFDerivAt)).sub_const S).sub
    (η.hasFDerivAt.comp z Y.hasFDerivAt)
  refine h.congr_fderiv ?_
  symm
  apply ContinuousLinearMap.ext
  intro v
  change t v • (one : H d) + sandwich (invH (X z)) (X v) - η (Y v) =
    t v • (one : H d) - (-sandwich (invH (X z)) (X v)) - η (Y v)
  module

lemma hasFDerivAt_stationaryPart (X P Q : E →L[ℝ] H d)
    (ε : ℝ) (η : H d →L[ℝ] H d) (z : E) (hX : X z ∈ pd d) :
    HasFDerivAt (fun v => sandwich (invH (X v)) (P v) - η (Q v) - ε • (one : H d))
      (((sandwichCLM (invH (X z))).comp P : E →L[ℝ] H d) - η.comp Q -
        ((jordanCLM (invH (X z)) (sandwich (invH (X z)) (P z))).comp X : E →L[ℝ] H d)) z := by
  have h := (((hasFDerivAt_invSandwich (X z) (P z) hX).comp z
    (X.hasFDerivAt.prodMk P.hasFDerivAt)).sub
    (η.hasFDerivAt.comp z Q.hasFDerivAt)).sub_const (ε • (one : H d))
  refine h.congr_fderiv ?_
  symm
  apply ContinuousLinearMap.ext
  intro v
  change sandwich (invH (X z)) (P v) - η (Q v) -
      jordanCLM (invH (X z)) (sandwich (invH (X z)) (P z)) (X v) =
    -jordanCLM (invH (X z)) (sandwich (invH (X z)) (P z)) (X v) +
      sandwich (invH (X z)) (P v) - η (Q v)
  module

lemma contDiffAt_tightPart {n : WithTop ℕ∞} {t : E → ℝ} {X Y S : E → H d}
    {η : E → (H d →L[ℝ] H d)} {z : E}
    (ht : ContDiffAt ℝ n t z) (hX : ContDiffAt ℝ n X z) (hY : ContDiffAt ℝ n Y z)
    (hS : ContDiffAt ℝ n S z) (hη : ContDiffAt ℝ n η z) (hpos : X z ∈ pd d) :
    ContDiffAt ℝ n (fun v => t v • (one : H d) - invH (X v) - S v - η v (Y v)) z :=
  (((ht.smul contDiffAt_const).sub ((contDiffAt_invH hpos).comp z hX)).sub hS).sub
    (hη.clm_apply hY)

lemma contDiffAt_stationaryPart {n : WithTop ℕ∞} {X P Q : E → H d}
    {η : E → (H d →L[ℝ] H d)} {z : E} (ε : ℝ)
    (hX : ContDiffAt ℝ n X z) (hP : ContDiffAt ℝ n P z) (hQ : ContDiffAt ℝ n Q z)
    (hη : ContDiffAt ℝ n η z) (hpos : X z ∈ pd d) :
    ContDiffAt ℝ n (fun v => sandwich (invH (X v)) (P v) - η v (Q v) - ε • (one : H d)) z :=
  (((contDiffAt_invSandwich (X z) (P z) hpos).comp z (hX.prodMk hP)).sub
    (hη.clm_apply hQ)).sub contDiffAt_const

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Vars
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupVars
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealVars
lemma hasFDerivAt_kktSystem (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) (z : Vars d)
    (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d) :
    HasFDerivAt (kktSystem ε S η)
      (CurrentKS.KKT.jacobian (identityPair d)
        (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) η))
        (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z))) z := by
  have hr := (((innerSL ℝ (identityPair d)).hasFDerivAt.comp z (pCoord d).hasFDerivAt).sub_const 1)
  have hfx := hasFDerivAt_tightPart (tCoord d) (xCoord d) (yCoord d) S η z hX
  have hfy := hasFDerivAt_tightPart (tCoord d) (yCoord d) (xCoord d) (-S) η z hY
  have hfu := (pairEquiv d).symm.hasFDerivAt.comp z (hfx.prodMk hfy)
  have hgx := hasFDerivAt_stationaryPart (xCoord d) (mCoord d) (nCoord d) ε η z hX
  have hgy := hasFDerivAt_stationaryPart (yCoord d) (nCoord d) (mCoord d) ε η z hY
  have hgp := (pairEquiv d).symm.hasFDerivAt.comp z (hgx.prodMk hgy)
  have hf := hr.prodMk (hfu.prodMk hgp)
  simp only [sub_neg_eq_add] at hf
  convert hf using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply (pairEquiv d).injective
      apply Prod.ext
      · change sandwich (invH (xCoord d z)) (xCoord d v) - η (yCoord d v) +
          tCoord d v • (Hermitian.one : H d) =
          tCoord d v • (Hermitian.one : H d) + sandwich (invH (xCoord d z)) (xCoord d v) - η (yCoord d v)
        module
      · change sandwich (invH (yCoord d z)) (yCoord d v) - η (xCoord d v) +
          tCoord d v • (Hermitian.one : H d) =
          tCoord d v • (Hermitian.one : H d) + sandwich (invH (yCoord d z)) (yCoord d v) - η (xCoord d v)
        module
    · rfl

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Parameters
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ}

section

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p4
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p4
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p4
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupParameters
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealParameters
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupVars_1
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealVars_1
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupProdParametersVars
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealProdParametersVars
lemma contDiffAt_kktGiven {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {S : E → H d} {η : E → (H d →L[ℝ] H d)}
    {v : E → Vars d} {b : E} (ε : ℝ)
    (hS : ContDiffAt ℝ n S b) (hη : ContDiffAt ℝ n η b) (hv : ContDiffAt ℝ n v b)
    (hX : xCoord d (v b) ∈ pd d) (hY : yCoord d (v b) ∈ pd d) :
    ContDiffAt ℝ n (fun a => kktSystem ε (S a) (η a) (v a)) b := by
  have ht := (tCoord d).contDiff.contDiffAt.comp b hv
  have hx := (xCoord d).contDiff.contDiffAt.comp b hv
  have hy := (yCoord d).contDiff.contDiffAt.comp b hv
  have hm := (mCoord d).contDiff.contDiffAt.comp b hv
  have hn := (nCoord d).contDiff.contDiffAt.comp b hv
  have hr := (((innerSL ℝ (identityPair d)).contDiff.contDiffAt.comp b
      ((pCoord d).contDiff.contDiffAt.comp b hv)).sub (contDiffAt_const (c := (1 : ℝ))))
  have hfx := contDiffAt_tightPart ht hx hy hS hη hX
  have hfy := contDiffAt_tightPart ht hy hx hS.neg hη hY
  have hfu := (pairEquiv d).symm.contDiff.contDiffAt.comp b (hfx.prodMk hfy)
  have hgx := contDiffAt_stationaryPart ε hx hm hn hη hX
  have hgy := contDiffAt_stationaryPart ε hy hn hm hη hY
  have hgp := (pairEquiv d).symm.contDiff.contDiffAt.comp b (hgx.prodMk hgy)
  have hh := hr.prodMk (hfu.prodMk hgp)
  simp only [sub_neg_eq_add] at hh
  exact hh

end

end CurrentKS.Variational

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ObjectiveVarsCLM
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p2
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p2
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p2
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupPairHilbert_1
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealPairHilbert_1
private local instance instTopologicalSpacePairHilbert_r9969c5_1 : TopologicalSpace (PairHilbert d) :=
  (inferInstance : NormedAddCommGroup (PairHilbert d)).toUniformSpace.toTopologicalSpace
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupVars_3
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealVars_3
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceVars_p4
lemma fderiv_kkt_parameter_right (ε : ℝ) (S : E → H d) (η : E → H d →L[ℝ] H d)
    (b : E) (z : Vars d) (hS : ContDiffAt ℝ 3 S b) (hη : ContDiffAt ℝ 3 η b)
    (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d) (u : Vars d) :
    fderiv ℝ (fun v : E × Vars d => kktSystem ε (S v.1) (η v.1) v.2) (b,z) (0,u) =
      CurrentKS.KKT.jacobian (identityPair d)
        (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) (η b)))
        (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z)) u := by
  let F := fun v : E × Vars d => kktSystem ε (S v.1) (η v.1) v.2
  have hF : ContDiffAt ℝ 3 F (b,z) := contDiffAt_kktGiven ε
    (hS.comp (b,z) (contDiffAt_fst)) (hη.comp (b,z) (contDiffAt_fst))
    contDiffAt_snd hX hY
  have hi : HasFDerivAt (fun w : Vars d => (b,w)) (ContinuousLinearMap.inr ℝ E (Vars d)) z := by
    convert (hasFDerivAt_const b z).prodMk (hasFDerivAt_id z) using 1 <;> rfl
  have hh := (hF.differentiableAt (by norm_num)).hasFDerivAt.comp z hi
  have he := hh.unique (hasFDerivAt_kktSystem ε (S b) (η b) z hX hY)
  exact congrArg (fun L : Vars d →L[ℝ] Vars d => L u) he

lemma kkt_curve_derivatives_oai (ε : ℝ) (S : E → H d) (η : E → H d →L[ℝ] H d)
    (b h : E) (hS : ContDiffAt ℝ 3 S b) (hη : ContDiffAt ℝ 3 η b)
    (z : Vars d) (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d)
    (J : Vars d ≃L[ℝ] Vars d)
    (hJ : ∀ u,J u=CurrentKS.KKT.jacobian (identityPair d)
      (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) (η b)))
      (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z)) u)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hJinv : ‖J.symm.toContinuousLinearMap‖ ≤ A) (hh : ‖h‖ ≤ 1)
    (hFB : JetBound (fun v : E × Vars d => kktSystem ε (S v.1) (η v.1) v.2) (b,z) D)
    (c : ℝ → Vars d) (hc : ContDiffAt ℝ 3 c 0) (hc0 : c 0=z)
    (heq : (fun t => kktSystem ε (S (b+t • h)) (η (b+t • h)) (c t)) =ᶠ[𝓝 0] (fun _ => 0)) :
    ‖iteratedDeriv 2 c 0‖ ≤ A*D*(1+A*D)^2 ∧
    ‖iteratedDeriv 3 c 0‖ ≤ A*D*((1+A*D)^3+3*(1+A*D)*(A*D*(1+A*D)^2)) := by
  let F := fun v : E × Vars d => kktSystem ε (S v.1) (η v.1) v.2
  have hF : ContDiffAt ℝ 3 F (b,z) := contDiffAt_kktGiven ε
    (hS.comp (b,z) contDiffAt_fst) (hη.comp (b,z) contDiffAt_fst) contDiffAt_snd hX hY
  have hfj (u : Vars d) : fderiv ℝ F (b+(0:ℝ) • h,c 0) (0,u)=J u := by
    simp only [zero_smul,add_zero,hc0]
    exact (fderiv_kkt_parameter_right ε S η b z hS hη hX hY u).trans (hJ u).symm
  have hF₁ : ‖fderiv ℝ F (b,z)‖ ≤ D := by
    simpa only [norm_iteratedFDeriv_one] using hFB 1 (by norm_num)
  have hb := CurrentKS.Implicit.graph_bounds F b h c 0
    (by simpa only [zero_smul,add_zero,hc0] using hF) hc heq J hfj hA hD hJinv hh
    (by simpa only [zero_smul,add_zero,hc0] using hF₁)
    (by simpa only [zero_smul,add_zero,hc0] using hFB 2 (by norm_num))
    (by simpa only [zero_smul,add_zero,hc0] using hFB 3 (by norm_num))
  exact hb.2

end
end CurrentKS.Variational

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CurrentKS.Variational.kkt_curve_derivatives_oai.{u_1} := @OAI.CurrentKS.Variational.kkt_curve_derivatives_oai.{u_1}
