-- Prove2me | solution 1 for OAI.Kadison.RelativeCornerQuantization.exists_relative_centered_compression
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:31:38.457422+00:00
-- url     : https://prove2.me/submissions/39a38b3d-9ea5-4f1e-ae80-dc68bf61fa44

import Mathlib
import Definitions.Def_OAIQ039C022
import Definitions.Def_OAIQ039C029
import Theorems.Thm_OAI_Kadison_LocalQuantization_exists_centered_compression
import Theorems.Thm_OAI_Kadison_RelativeCornerQuantization_exists_polar_cut

section
-- module Solutions.OAIQ039_CM.Commutator_TracialL2Tools
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.TracialL2

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

lemma norm_nonneg (a : A) : 0≤norm τ a := _root_.norm_nonneg _

end Kadison.TracialL2

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RelativeCornerQuantization
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

namespace Kadison.RelativeCornerQuantization

open TracialL2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

section Quantization

variable {J : Type*} [Fintype J]

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, LinearOrder (ι n)]
  [∀ n, Nonempty (ι n)]

variable (stage : ∀ n, Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ}, n ≤ m → (stage n).range ≤ (stage m).range)

include hτ hmono in
theorem exists_relative_centered_compression_oai
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M, (∀ n (x : Matrix (ι n) (ι n) ℂ), stage n x*b=b*stage n x) →
      ∃ c : ℂ, b=algebraMap ℂ M c)
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (N : VonNeumannAlgebra H)
    (hstage : ∀ n a, (stage n a : H →L[ℂ] H)∈N)
    (p : M) (hpN : (p : H →L[ℂ] H)∈N) (hp : IsStarProjection p)
    (hpt : 0<(τ p).re)
    (x : J → M) (hx : ∀ j, τ (x j)=0) (hpx : ∀ j,p*x j=x j) (hxp : ∀ j,x j*p=x j)
    {ε η : ℝ} (hε : 0<ε) (hη : 0<η) :
    ∃ f : M, (f : H →L[ℂ] H)∈N ∧ IsStarProjection f ∧ f ≤ p ∧
      0<(τ f).re ∧ (τ f).re<η ∧ ∀ j, norm τ (f*x j*f)^2<ε^2*(τ f).re := by
  classical
  let t : ℝ := (τ p).re
  have ht : 0<t := hpt
  let c : ℝ := (Real.sqrt t)⁻¹
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr ht)
  have hct : c*c*t=1 := by
    dsimp [c]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr ht)]
    nlinarith only [Real.sq_sqrt ht.le]
  let B : ℝ := ∑ j, ‖x j‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => _root_.norm_nonneg (x j))
  have hxB (j : J) : ‖x j‖ ≤ B :=
    Finset.single_le_sum (fun i _ => _root_.norm_nonneg (x i)) (Finset.mem_univ j)
  let K : ℝ := c^2+(1+c)*B*c^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let δ : ℝ := min (1/(2*(c^2+1))) (ε/(2*(K+1)))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδc : c^2*δ ≤ 1/2 := by
    have h := (le_div_iff₀ (by positivity : 0<2*(c^2+1))).mp (min_le_left
      (1/(2*(c^2+1))) (ε/(2*(K+1))))
    change δ*(2*(c^2+1)) ≤ 1 at h
    nlinarith only [h,hδ]
  have hδK : K*δ ≤ ε/2 := by
    have h := (le_div_iff₀ (by positivity : 0<2*(K+1))).mp (min_le_right
      (1/(2*(c^2+1))) (ε/(2*(K+1))))
    change δ*(2*(K+1)) ≤ ε at h
    nlinarith only [h,hδ]
  let z : Option J → M := fun j => match j with
    | none => p-t • (1:M)
    | some j => x j
  have htrace : τ p=(t:ℂ) := Complex.ext rfl (τ.map_nonneg hp.nonneg).2.symm
  have hz : ∀ j,τ (z j)=0 := by
    intro j
    cases j with
    | none => simp [z,map_sub,PositiveLinearMap.map_smul_of_tower,hone,htrace]
    | some j => exact hx j
  obtain ⟨n,q,hqstage,hq,hqt,hqη,hsum⟩ :=
    LocalQuantization.exists_centered_compression M τ hτ stage hmono hnormal hfaith hone hirr
      hgrow z hz hδ hη
  have hqN : (q : H →L[ℂ] H)∈N := by
    obtain ⟨a,rfl⟩ := hqstage
    exact hstage n a
  have hsum' : (∑ j, norm τ (q*z j*q)^2)<δ^2*(τ q).re := by
    simpa only [TracialGNS.algebraVector_apply,UniformSpace.Completion.norm_coe,TracialL2.norm] using hsum
  let s : ℝ := Real.sqrt (τ q).re
  have hs : 0 < s := Real.sqrt_pos.mpr hqt
  have hs2 : s^2=(τ q).re := Real.sq_sqrt hqt.le
  have hsmall (j : Option J) : norm τ (q*z j*q) ≤ δ*s := by
    apply (sq_le_sq₀ (norm_nonneg τ _) (mul_nonneg hδ.le hs.le)).mp
    have hj : norm τ (q*z j*q)^2 ≤ ∑ i,norm τ (q*z i*q)^2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (norm τ (q*z i*q))) (Finset.mem_univ j)
    rw [mul_pow,hs2]
    exact hj.trans hsum'.le
  obtain ⟨f,hf,hfp,hfq,hker,hcomp,hN⟩ := exists_polar_cut M τ hτ p q hp hq hc.le hct
  have hd : c^2*norm τ (q*(p-t • (1:M))*q) ≤ s/2 := by
    calc
      _ ≤ c^2*(δ*s) := mul_le_mul_of_nonneg_left (hsmall none) (sq_nonneg c)
      _=(c^2*δ)*s := by ring
      _ ≤ (1/2)*s := mul_le_mul_of_nonneg_right hδc hs.le
      _=_ := by ring
  have hd2 : (c^2*norm τ (q*(p-t • (1:M))*q))^2 ≤ s^2/4 := by
    calc
      _ ≤ (s/2)^2 := (sq_le_sq₀ (mul_nonneg (sq_nonneg c) (norm_nonneg τ _)) (by positivity)).mpr hd
      _=_ := by ring
  have hqt4 : (τ q).re/4<(τ f).re := by
    rw [hs2] at hd2
    have hh := hker.trans hd2
    linarith only [hh,hqt]
  refine ⟨f,hN N hpN hqN,hf,hfp,lt_trans (by positivity) hqt4,hfq.trans_lt hqη,?_⟩
  intro j
  have hnorm : norm τ (f*x j*f) ≤ (ε/2)*s := by
    calc
      _ ≤ c^2*norm τ (q*x j*q)+(1+c)*‖x j‖*c^2*norm τ (q*(p-t • (1:M))*q) :=
        hcomp (x j) (hpx j) (hxp j)
      _ ≤ c^2*(δ*s)+(1+c)*B*c^2*(δ*s) := by
        gcongr
        · exact hsmall (some j)
        · exact norm_nonneg τ _
        · exact hxB j
        · exact hsmall none
      _=(K*δ)*s := by dsimp [K]; ring
      _ ≤ (ε/2)*s := mul_le_mul_of_nonneg_right hδK hs.le
  calc
    _ ≤ ((ε/2)*s)^2 := (sq_le_sq₀ (norm_nonneg τ _) (by positivity)).mpr hnorm
    _=ε^2*((τ q).re/4) := by rw [mul_pow,hs2]; ring
    _<ε^2*(τ f).re := mul_lt_mul_of_pos_left hqt4 (sq_pos_of_pos hε)

end Quantization

end Kadison.RelativeCornerQuantization

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.RelativeCornerQuantization.exists_relative_centered_compression_oai.{u_1, u_2, u_3} := @OAI.Kadison.RelativeCornerQuantization.exists_relative_centered_compression_oai.{u_1, u_2, u_3}
