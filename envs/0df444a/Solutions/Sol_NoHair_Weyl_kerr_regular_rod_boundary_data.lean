-- Prove2me | solution 1 for NoHair.Weyl.kerr_regular_rod_boundary_data
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:41:15.435038+00:00
-- url     : https://prove2.me/submissions/a15c1912-5b44-47fa-87e6-3689439f11c6

import Definitions.Def_NoHair_regularRodBoundaryData
import Theorems.Thm_NoHair_Weyl_prolate_coordinate_differentials

noncomputable section

open NoHair NoHair.Weyl Set
open scoped ContDiff

private def rodAngleDerivative (f : OrbitPoint → ℝ) (z : OrbitPoint) : ℝ :=
  fderiv ℝ f z (0,1)

private lemma slope_cont {f : OrbitPoint → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (rodAngleDerivative f) :=
  (hf.continuous_fderiv (by simp)).clm_apply continuous_const

private lemma slope_der {f : OrbitPoint → ℝ} (hf : ContDiff ℝ ∞ f) (q c : ℝ) :
    HasDerivAt (fun t => f (q,t)) (rodAngleDerivative f (q,c)) c := by
  have hd : HasDerivAt (fun t : ℝ => (q,t)) (0,1) c :=
    (hasDerivAt_const c q).prodMk (hasDerivAt_id c)
  exact ((hf.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt c hd

theorem solution (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    Nonempty (RegularRodBoundaryData (kerrErnst m a) m (Real.sqrt (m^2-a^2)) (m*a)) := by
  let ℓ := Real.sqrt (m^2-a^2)
  let S := fun z : OrbitPoint => 1-z.2^2
  let D := fun z : OrbitPoint => 1+a^2*z.2^2*z.1^2
  let B := fun z : OrbitPoint => 1+a^2*z.1^2+2*m*a^2*z.1^3*S z/D z
  let A := fun z : OrbitPoint => S z*B z
  let V := fun z : OrbitPoint => 2*m*a^3*z.1^4*z.2*(S z)^2/D z
  have hD (z : OrbitPoint) : 0 < D z := by dsimp [D]; positivity
  have cB : ContDiff ℝ ∞ B := by dsimp [B,D,S]; fun_prop (disch := intros; positivity)
  have cA : ContDiff ℝ ∞ A := by dsimp only [A]; exact (by dsimp [S]; fun_prop : ContDiff ℝ ∞ S).mul cB
  have cV : ContDiff ℝ ∞ V := by dsimp [V,D,S]; fun_prop (disch := intros; positivity)
  have sd (c : ℝ) : HasDerivAt (fun t : ℝ => 1-t^2) (-2*c) c := by
    simpa only [Nat.cast_ofNat,Nat.reduceSub,pow_one,neg_mul] using (hasDerivAt_pow 2 c).const_sub (1:ℝ)
  have edge (q c : ℝ) (hc : 1-c^2=0) : rodAngleDerivative A (q,c) = -2*c*(1+a^2*q^2) := by
    have had := slope_der cA q c
    have ht := (sd c).mul (slope_der cB q c)
    change HasDerivAt (fun t => (1-t^2)*B (q,t)) _ c at had
    have he := had.unique ht
    simpa [B,S,hc] using he
  refine ⟨{ normData := A, twistData := V, normSlope := rodAngleDerivative A, twistSlope := rodAngleDerivative V
            normSlope_continuous := (slope_cont cA).continuousOn
            twistSlope_continuous := (slope_cont cV).continuousOn
            norm_derivative := fun z _ => slope_der cA z.1 z.2
            twist_derivative := fun z _ => slope_der cV z.1 z.2
            values := ?_, poles := ?_, interior_pos := ?_, infinity := ?_ }⟩
  · intro p
    let R := prolateRadius ℓ p
    let r := m+R
    let c := p.2/R
    have hr : 0 < r := add_pos hm.1 ((prolate_coordinate_differentials ℓ).2.2 p).1
    have hQ : 0 < r^2+a^2*c^2 := by positivity
    have hden := hD (1/r,c)
    change 0 < 1+a^2*c^2*(1/r)^2 at hden
    change A (1/r,c)=kerrAxialNorm m a r c/r^2 ∧
      V (1/r,c)=(kerrAxialTwist m a r c-2*(m*a)*(3*c-c^3))/r^2
    dsimp [A,B,V,D,S,kerrAxialNorm,kerrAxialTwist]
    constructor <;> field_simp [hr.ne',hQ.ne',hden.ne'] <;> ring
  · intro q hq
    have hlo := edge q (-1) (by norm_num)
    have hhi := edge q 1 (by norm_num)
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simp [A,S]
    · simp [A,S]
    · simp [V,S]
    · simp [V,S]
    · rw [hlo]; nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg q)]
    · rw [hhi]; nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg q)]
  · intro q hq c hc
    have hS : 0 < S (q,c) := by
      change 0 < 1-c^2
      nlinarith only [mul_pos (sub_pos.mpr hc.2) (sub_pos.mpr hc.1)]
    have hq0:=hq.1
    have hm0:=hm.1
    have hd:=hD (q,c)
    change 0 < S (q,c) * (1+a^2*q^2+2*m*a^2*q^3*S (q,c)/D (q,c))
    positivity
  · intro c _
    simp [A,B,S,V,D]
