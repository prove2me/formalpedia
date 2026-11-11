-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Ellipsoid.robust_cut_det_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:12:53.041217+00:00
-- url     : https://prove2.me/submissions/4a561beb-70aa-4731-a08a-d8d434846f4b

import Mathlib
import Definitions.Def_Q238K004

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_KindRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open scoped InnerProductSpace

lemma determinant_growth (n : ℕ) (hn : 2≤n) :
    1+1/(n:ℝ) ≤ (( (n:ℝ)^2-1)/(n:ℝ)^2)^n * (((n:ℝ)+1)/((n:ℝ)-1)) := by
  have hp : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hn0 : (n:ℝ)≠0 := by positivity
  have hnm : (n:ℝ)-1≠0 := by linarith
  have hneg : (-1:ℝ)≤ -(1/(n:ℝ)^2) := by
    have hh : (1:ℝ)≤(n:ℝ)^2 := by nlinarith
    have hq : 1/(n:ℝ)^2≤1 := (div_le_one (by positivity)).mpr hh
    linarith
  have hb := one_add_mul_le_pow (show (-2:ℝ)≤ -(1/(n:ℝ)^2) by linarith) n
  have hbase : 1 + -(1/(n:ℝ)^2) = ((n:ℝ)^2-1)/(n:ℝ)^2 := by
    field_simp
    ring
  have hleft : 1+(n:ℝ)*-(1/(n:ℝ)^2) = 1-1/(n:ℝ) := by
    field_simp
    ring
  have hpow : 1-1/(n:ℝ) ≤ (((n:ℝ)^2-1)/(n:ℝ)^2)^n := by
    rwa [hbase,hleft] at hb
  calc
    _ = (1-1/(n:ℝ))*(((n:ℝ)+1)/((n:ℝ)-1)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (div_nonneg (by positivity) (by linarith))

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_CutMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma cutMatrix_pos (d : ℝ) (hd : 1<d) (M : Matrix V V ℝ) (hM : M.PosDef)
    (u : V → ℝ) : (cutMatrix d M u).PosDef := by
  have hα : 0<(d^2-1)/d^2 := div_pos (by nlinarith) (by positivity)
  have hβ : 0≤2*(d+1)/d^2 := by positivity
  have hh : (vecMulVec (M *ᵥ u) (M *ᵥ u)).PosSemidef := by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star (M *ᵥ u)
  exact (hM.smul hα).add_posSemidef (hh.smul hβ)

lemma rank_one_det (M : Matrix V V ℝ) (hM : M.PosDef) (u : V → ℝ)
    (hu : quad M u=1) (γ : ℝ) :
    (M+γ • vecMulVec (M *ᵥ u) (M *ᵥ u)).det=M.det*(1+γ) := by
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr (ne_of_gt hM.det_pos)
  have hinv : M⁻¹ *ᵥ (M *ᵥ u)=u := by
    rw [mulVec_mulVec,nonsing_inv_mul _ hunit,one_mulVec]
  rw [←smul_vecMulVec,vecMulVec_eq Unit,det_add_replicateCol_mul_replicateRow hunit]
  congr 1
  rw [det_unique]
  simp only [Matrix.add_apply,one_apply_eq]
  rw [Matrix.mul_assoc,←replicateCol_mulVec,mulVec_smul,hinv,
    replicateRow_mul_replicateCol_apply,dotProduct_smul,smul_eq_mul,
    dotProduct_comm (M *ᵥ u) u]
  change 1+γ*quad M u=1+γ
  rw [hu,mul_one]

lemma cutMatrix_det (d : ℝ) (hd : 1<d) (M : Matrix V V ℝ) (hM : M.PosDef)
    (u : V → ℝ) (hu : quad M u=1) :
    (cutMatrix d M u).det = (((d^2-1)/d^2)^(Fintype.card V)*(d+1)/(d-1))*M.det := by
  have hd0 : d≠0 := by linarith
  have hdm : d-1≠0 := by linarith
  have hds : d^2-1≠0 := by nlinarith
  have he : cutMatrix d M u = ((d^2-1)/d^2) •
      (M+(2/(d-1)) • vecMulVec (M *ᵥ u) (M *ᵥ u)) := by
    unfold cutMatrix
    rw [smul_add,smul_smul]
    congr 2
    field_simp
    ring
  rw [he,det_smul,rank_one_det M hM u hu]
  have hc : 1+2/(d-1)=(d+1)/(d-1) := by field_simp <;> ring
  rw [hc]
  ring

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_QuadSmulVec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

open Matrix
open scoped Matrix MatrixOrder
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma det_ge_one (M : Matrix V V ℝ) (hM : M.IsHermitian)
    (hbound : (M-1).PosSemidef) : 1≤M.det := by
  have he (i : V) : 1≤hM.eigenvalues i := by
    let v := hM.eigenvectorBasis i
    have hv : star (v : V → ℝ) ⬝ᵥ (v : V → ℝ)=1 := by
      rw [dotProduct_comm,←EuclideanSpace.inner_eq_star_dotProduct,inner_self_eq_norm_sq_to_K]
      simp only [v,hM.eigenvectorBasis.orthonormal.1 i,one_pow,algebraMap.coe_one]
    have hp := hbound.dotProduct_mulVec_nonneg (v : V → ℝ)
    simp only [sub_mulVec,one_mulVec,dotProduct_sub,hv] at hp
    have hval := hM.eigenvalues_eq i
    change hM.eigenvalues i = star (v : V → ℝ) ⬝ᵥ (M *ᵥ (v : V → ℝ)) at hval
    linarith
  rw [hM.det_eq_prod_eigenvalues]
  exact Finset.one_le_prod fun index _ => by simpa using he index

lemma det_mono_posDef (A B : Matrix V V ℝ) (hA : A.PosDef)
    (hBA : (B-A).PosSemidef) : A.det≤B.det := by
  let S : Matrix V V ℝ := CFC.sqrt A
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hsq : S*S=A := by simpa only [S,pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
  have hSd : S.det≠0 := by
    intro he
    have hh := congrArg Matrix.det hsq
    rw [det_mul,he,zero_mul] at hh
    linarith [hA.det_pos]
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hSd
  let K := S⁻¹
  have hKherm : K.IsHermitian := hS.inv.isHermitian
  have hconj : K*A*K=1 := by
    rw [←hsq]
    change S⁻¹*(S*S)*S⁻¹=1
    rw [←Matrix.mul_assoc,nonsing_inv_mul _ hSu,one_mul,mul_nonsing_inv _ hSu]
  have hC : (K*B*K-1).PosSemidef := by
    have hh := hBA.mul_mul_conjTranspose_same K
    rw [hKherm.eq,mul_sub,sub_mul,hconj] at hh
    exact hh
  have hCh : (K*B*K).IsHermitian := by
    simpa only [sub_add_cancel] using hC.isHermitian.add (isHermitian_one (n:=V) (α:=ℝ))
  have hd := det_ge_one (K*B*K) hCh hC
  have hone := congrArg Matrix.det hconj
  simp only [det_mul,det_one] at hd hone
  have hK0 : K.det≠0 := by
    change (S⁻¹).det≠0
    rw [det_nonsing_inv]
    exact Ring.isUnit_iff_inverse_ne_zero.mp hSu
  have hp : 0<K.det^2 := sq_pos_of_ne_zero hK0
  have hh : K.det^2*A.det≤K.det^2*B.det := by nlinarith [hd]
  exact (mul_le_mul_iff_right₀ hp).mp (by simpa only [mul_comm] using hh)

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RealVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma cutMatrix_grows (M : Matrix V V ℝ) (hM : M.PosDef) (u : V → ℝ)
    (hu : quad M u=1) (hn : 2≤Fintype.card V) :
    (1+1/(Fintype.card V:ℝ))*M.det ≤ (cutMatrix (Fintype.card V) M u).det := by
  rw [cutMatrix_det _ (by exact_mod_cast (show 1<Fintype.card V by omega)) M hM u hu]
  have hh := mul_le_mul_of_nonneg_right (determinant_growth (Fintype.card V) hn) hM.det_pos.le
  simpa only [mul_div_assoc] using hh

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InflationPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma inflation_pos (n : ℕ) (hn : 1≤n) : 0<1-1/(8*(n:ℝ)^2) := by
  have hp : (1:ℝ)≤n := by exact_mod_cast hn
  have hb : 1/(8*(n:ℝ)^2)<1 := (div_lt_one (by positivity)).mpr (by nlinarith)
  linarith

lemma robust_scalar_growth (n : ℕ) (hn : 1≤n) :
    1+1/(2*(n:ℝ))≤(1-1/(8*(n:ℝ)^2))^(2*n)*(1+1/(n:ℝ)) := by
  have hp : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (n:ℝ)≠0 := by positivity
  have hq : 1/(8*(n:ℝ)^2)≤1 := (div_le_one (by positivity)).mpr (by nlinarith)
  have hb := one_add_mul_le_pow (show (-2:ℝ)≤ -(1/(8*(n:ℝ)^2)) by linarith) (2*n)
  have he : 1+(2*n:ℕ)*( -(1/(8*(n:ℝ)^2)))=1-1/(4*(n:ℝ)) := by
    push_cast
    field_simp
    ring
  have hl : 1-1/(4*(n:ℝ))≤(1-1/(8*(n:ℝ)^2))^(2*n) := by
    simpa only [he,sub_eq_add_neg] using hb
  calc
    _ ≤ (1-1/(4*(n:ℝ)))*(1+1/(n:ℝ)) := by
      have h : 0≤(n:ℝ)-1 := by linarith
      have heq : (1-1/(4*(n:ℝ)))*(1+1/(n:ℝ))-(1+1/(2*(n:ℝ)))=
          ((n:ℝ)-1)/(4*(n:ℝ)^2) := by field_simp <;> ring
      have hh : 0≤((n:ℝ)-1)/(4*(n:ℝ)^2) := div_nonneg h (by positivity)
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hl (by positivity)

lemma robust_cut_det_s238_oai (M R : Matrix V V ℝ) (hM : M.PosDef) (u : V → ℝ)
    (hu : quad M u=1) (hn : 2≤Fintype.card V)
    (hR : (R-(1-1/(8*(Fintype.card V:ℝ)^2)) •
      ((1-1/(8*(Fintype.card V:ℝ)^2)) • cutMatrix (Fintype.card V) M u)).PosSemidef) :
    (1+1/(2*(Fintype.card V:ℝ)))*M.det≤R.det := by
  let lam : ℝ := 1-1/(8*(Fintype.card V:ℝ)^2)
  have hlam : 0<lam := inflation_pos _ (by omega)
  have hcut : (cutMatrix (Fintype.card V) M u).PosDef :=
    cutMatrix_pos _ (by exact_mod_cast (show 1<Fintype.card V by omega)) M hM u
  have hd := det_mono_posDef (lam • (lam • cutMatrix (Fintype.card V) M u)) R
    ((hcut.smul hlam).smul hlam) hR
  simp only [Matrix.det_smul] at hd
  have hg := cutMatrix_grows M hM u hu hn
  have hlg := mul_le_mul_of_nonneg_left hg (pow_nonneg hlam.le (2*Fintype.card V))
  have hs := mul_le_mul_of_nonneg_right
    (robust_scalar_growth (Fintype.card V) (by omega)) hM.det_pos.le
  have he : lam^(2*Fintype.card V)=lam^(Fintype.card V)*lam^(Fintype.card V) := by
    rw [two_mul,pow_add]
  dsimp [lam] at he ⊢
  dsimp [lam] at hlg hd
  rw [he] at hlg hs
  nlinarith

end MetricKMedianRecovery.Ellipsoid

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.Ellipsoid.robust_cut_det_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.Ellipsoid.robust_cut_det_s238_oai.{u_1}
