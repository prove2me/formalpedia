-- Prove2me | solution 1 for LanglandsTunnell.Converse.DiscreteFamily.matrixCasimir_W
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/cf743f8f-46c3-57ea-882a-db8c06faf4e5

import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_DiscreteFamily_matrixCasimir_W

set_option autoImplicit false

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam RealArchParam.discrete RealArchParam.laplaceEigenvalue_discrete"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "DiscreteFamily.W"
namespace DiscreteFamily
p2m_export "LanglandsTunnell.Converse.DiscreteFamily" "nsq iy ix kap pexp prof detPow W"
p2m_open "LanglandsTunnell.Converse.DiscreteFamily LanglandsTunnell.Converse LanglandsTunnell"

local notation "M₂" => Matrix (Fin 2) (Fin 2) ℝ

private theorem det_eq (g : M₂) : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two g

private theorem nsq_nonneg (g : M₂) : 0 ≤ nsq g := by unfold nsq; positivity

private theorem nsq_pos_of_det_ne_zero {g : M₂} (h : g.det ≠ 0) : 0 < nsq g := by
  rcases (nsq_nonneg g).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have h0 : g 1 0 = 0 ∧ g 1 1 = 0 := by
      have := heq.symm
      unfold nsq at this
      constructor <;> nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    apply h
    rw [det_eq, h0.1, h0.2]; ring

end LanglandsTunnell.Converse.DiscreteFamily

end
end

section

set_option autoImplicit false

open Complex

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam RealArchParam.discrete RealArchParam.laplaceEigenvalue_discrete"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "DiscreteFamily.W"
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

namespace DiscreteFamily
p2m_export "LanglandsTunnell.Converse.DiscreteFamily" "nsq iy ix kap pexp prof detPow W"
namespace FlowCore
p2m_open "LanglandsTunnell.Converse.DiscreteFamily"

private theorem hasDerivAt_ofReal' (t : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
  simpa using (hasDerivAt_id t).ofReal_comp

private theorem hasDerivAt_affine (K α N J n₁ j₁ A₀ A₁ A₂ : ℂ) (m : ℕ) (hJ : J ≠ 0) :
    HasDerivAt (fun t : ℝ => K * Complex.exp (α * ((N + n₁ * (t : ℂ)) / (J + j₁ * (t : ℂ)))) *
        (A₀ + A₁ * (t : ℂ) + A₂ * (t : ℂ) ^ 2) / (J + j₁ * (t : ℂ)) ^ (m + 1))
      (K * Complex.exp (α * (N / J)) / J ^ (m + 1 + 2) *
        (α * (n₁ * J - N * j₁) * A₀ + J ^ 2 * A₁ - (m + 1) * j₁ * J * A₀)) 0 := by
  have ht := hasDerivAt_ofReal' 0
  have hN : HasDerivAt (fun t : ℝ => N + n₁ * (t : ℂ)) n₁ 0 := by
    simpa using (ht.const_mul n₁).const_add N
  have hJ' : HasDerivAt (fun t : ℝ => J + j₁ * (t : ℂ)) j₁ 0 := by
    simpa using (ht.const_mul j₁).const_add J
  have hJ0 : J + j₁ * ((0 : ℝ) : ℂ) ≠ 0 := by simpa using hJ
  have hz : HasDerivAt (fun t : ℝ => (N + n₁ * (t : ℂ)) / (J + j₁ * (t : ℂ))) ((n₁ * J - N * j₁) / J ^ 2) 0 := by
    have h := hN.div hJ' hJ0
    simp only [ofReal_zero, mul_zero, add_zero] at h
    exact h
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (α * ((N + n₁ * (t : ℂ)) / (J + j₁ * (t : ℂ)))))
      (Complex.exp (α * (N / J)) * (α * ((n₁ * J - N * j₁) / J ^ 2))) 0 := by
    have h := (hz.const_mul α).cexp
    simp only [ofReal_zero, mul_zero, add_zero] at h
    exact h
  have hP : HasDerivAt (fun t : ℝ => A₀ + A₁ * (t : ℂ) + A₂ * (t : ℂ) ^ 2) A₁ 0 := by
    have h := ((ht.const_mul A₁).const_add A₀).add ((ht.pow 2).const_mul A₂)
    simp at h
    exact h
  have hD : HasDerivAt (fun t : ℝ => (J + j₁ * (t : ℂ)) ^ (m + 1)) ((m + 1 : ℕ) * J ^ (m + 1 - 1) * j₁) 0 := by
    have h := hJ'.pow (m + 1)
    simp only [ofReal_zero, mul_zero, add_zero] at h
    exact h
  have hnum := (hexp.const_mul K).mul hP
  have hDm : (J + j₁ * ((0 : ℝ) : ℂ)) ^ (m + 1) ≠ 0 := by simpa using pow_ne_zero (m + 1) hJ
  have h := hnum.div hD hDm
  simp only [ofReal_zero, mul_zero, add_zero] at h
  convert h using 1
  · rfl
  · rfl
  simp only [Pi.mul_apply, ofReal_zero, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Nat.add_sub_cancel, Nat.cast_succ]
  field_simp
  ring

private theorem hasDerivAt_expo (K α np nm jp jm A B C : ℂ) (m : ℕ) (hJ : jp + jm ≠ 0) :
    HasDerivAt (fun t : ℝ => K * Complex.exp (α * ((np * (Real.exp t : ℂ) + nm * (Real.exp (-t) : ℂ)) /
          (jp * (Real.exp t : ℂ) + jm * (Real.exp (-t) : ℂ)))) *
        (A + B * (Real.exp t : ℂ) ^ 2 + C * (Real.exp (-t) : ℂ) ^ 2) /
          (jp * (Real.exp t : ℂ) + jm * (Real.exp (-t) : ℂ)) ^ (m + 1))
      (K * Complex.exp (α * ((np + nm) / (jp + jm))) / (jp + jm) ^ (m + 1 + 2) *
        (α * ((np - nm) * (jp + jm) - (np + nm) * (jp - jm)) * (A + B + C) + (jp + jm) ^ 2 * (2 * B - 2 * C) -
          (m + 1) * (jp - jm) * (jp + jm) * (A + B + C))) 0 := by
  have hE : HasDerivAt (fun t : ℝ => ((Real.exp t : ℝ) : ℂ)) 1 0 := by
    simpa using (Real.hasDerivAt_exp 0).ofReal_comp
  have hEm : HasDerivAt (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) (-1) 0 := by
    simpa using ((Real.hasDerivAt_exp (-(0 : ℝ))).comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))).ofReal_comp
  have hN : HasDerivAt (fun t : ℝ => np * (Real.exp t : ℂ) + nm * (Real.exp (-t) : ℂ)) (np - nm) 0 := by
    have h := (hE.const_mul np).add (hEm.const_mul nm)
    simp only [mul_one, mul_neg] at h
    simp [sub_eq_add_neg] at h ⊢
    exact h
  have hJ' : HasDerivAt (fun t : ℝ => jp * (Real.exp t : ℂ) + jm * (Real.exp (-t) : ℂ)) (jp - jm) 0 := by
    have h := (hE.const_mul jp).add (hEm.const_mul jm)
    simp only [mul_one, mul_neg] at h
    simp [sub_eq_add_neg] at h ⊢
    exact h
  have hJ0 : jp * ((Real.exp 0 : ℝ) : ℂ) + jm * ((Real.exp (-0) : ℝ) : ℂ) ≠ 0 := by simpa using hJ
  have hz : HasDerivAt (fun t : ℝ => (np * (Real.exp t : ℂ) + nm * (Real.exp (-t) : ℂ)) /
      (jp * (Real.exp t : ℂ) + jm * (Real.exp (-t) : ℂ)))
      (((np - nm) * (jp + jm) - (np + nm) * (jp - jm)) / (jp + jm) ^ 2) 0 := by
    have h := hN.div hJ' hJ0
    simp only [neg_zero, Real.exp_zero, ofReal_one, mul_one] at h
    exact h
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (α * ((np * (Real.exp t : ℂ) + nm * (Real.exp (-t) : ℂ)) /
      (jp * (Real.exp t : ℂ) + jm * (Real.exp (-t) : ℂ)))))
      (Complex.exp (α * ((np + nm) / (jp + jm))) *
        (α * (((np - nm) * (jp + jm) - (np + nm) * (jp - jm)) / (jp + jm) ^ 2))) 0 := by
    have h := (hz.const_mul α).cexp
    simp only [neg_zero, Real.exp_zero, ofReal_one, mul_one] at h
    exact h
  have hP : HasDerivAt (fun t : ℝ => A + B * (Real.exp t : ℂ) ^ 2 + C * (Real.exp (-t) : ℂ) ^ 2)
      (2 * B - 2 * C) 0 := by
    have h := (((hE.pow 2).const_mul B).const_add A).add ((hEm.pow 2).const_mul C)
    simp only [neg_zero, Real.exp_zero, ofReal_one, mul_one, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_neg]
      at h
    convert h using 1
    · rfl
    · rfl
    ring
  have hD : HasDerivAt (fun t : ℝ => (jp * (Real.exp t : ℂ) + jm * (Real.exp (-t) : ℂ)) ^ (m + 1))
      ((m + 1 : ℕ) * (jp + jm) ^ (m + 1 - 1) * (jp - jm)) 0 := by
    have h := hJ'.pow (m + 1)
    simp only [neg_zero, Real.exp_zero, ofReal_one, mul_one] at h
    exact h
  have hnum := (hexp.const_mul K).mul hP
  have hDm : (jp * ((Real.exp 0 : ℝ) : ℂ) + jm * ((Real.exp (-0) : ℝ) : ℂ)) ^ (m + 1) ≠ 0 := by
    simpa using pow_ne_zero (m + 1) hJ
  have h := hnum.div hD hDm
  simp only [neg_zero, Real.exp_zero, ofReal_one, mul_one] at h
  convert h using 1
  · rfl
  · rfl
  simp only [Pi.mul_apply, neg_zero, Real.exp_zero, ofReal_one, mul_one, one_pow, Nat.add_sub_cancel, Nat.cast_succ]
  field_simp
  ring

end DiscreteFamily.FlowCore

namespace DiscreteFamily
p2m_export "LanglandsTunnell.Converse.DiscreteFamily" "nsq iy ix kap pexp prof detPow W"
p2m_open "LanglandsTunnell.Converse.DiscreteFamily"

p2m_open "LanglandsTunnell.Converse.ArchR LanglandsTunnell.Converse.ArchCasimir AutomorphicForm"

local notation "M₂" => Matrix (Fin 2) (Fin 2) ℝ

section ClosedForm

variable (u₀ : ℂ) (k₀ : ℕ)

private def jfac (g : M₂) : ℂ := (g 1 0 : ℂ) * I + (g 1 1 : ℂ)

private def nfac (g : M₂) : ℂ := (g 0 0 : ℂ) * I + (g 0 1 : ℂ)

private def tpI : ℂ := 2 * (Real.pi : ℂ) * I

private def Kf (g : M₂) : ℂ := ((g.det ^ pexp k₀ : ℝ) : ℂ) * detPow u₀ g

private def Wcl (g : M₂) : ℂ :=
  if 0 < g.det then Kf u₀ k₀ g * Complex.exp (tpI * (nfac g / jfac g)) / jfac g ^ (k₀ + 1) else 0

private theorem jfac_ne_zero {g : M₂} (h : g.det ≠ 0) : jfac g ≠ 0 := by
  intro h0
  have hre := congrArg Complex.re h0
  have him := congrArg Complex.im h0
  simp [jfac] at hre him
  apply h
  rw [det_eq, hre, him]; ring

private theorem jfac_mul_conj (g : M₂) : jfac g * ((g 1 1 : ℂ) - (g 1 0 : ℂ) * I) = (nsq g : ℂ) := by
  unfold jfac nsq; push_cast
  have hI : I * I = -1 := I_mul_I
  linear_combination (-(g 1 0 : ℂ) ^ 2) * hI

private theorem nfac_div_jfac {g : M₂} (h : g.det ≠ 0) : nfac g / jfac g = (ix g : ℂ) + (iy g : ℂ) * I := by
  have hj := jfac_ne_zero h
  have hn : (nsq g : ℂ) ≠ 0 := by exact_mod_cast (nsq_pos_of_det_ne_zero h).ne'
  rw [div_eq_iff hj]
  have key : nfac g * ((g 1 1 : ℂ) - (g 1 0 : ℂ) * I) = (((ix g : ℂ) + (iy g : ℂ) * I) * jfac g) *
      ((g 1 1 : ℂ) - (g 1 0 : ℂ) * I) := by
    rw [mul_assoc, jfac_mul_conj]
    unfold nfac ix iy
    rw [det_eq]
    push_cast
    field_simp
    have hI : I * I = -1 := I_mul_I
    linear_combination (-((g 0 0 : ℂ) * (g 1 0 : ℂ))) * hI
  have hc : ((g 1 1 : ℂ) - (g 1 0 : ℂ) * I) ≠ 0 := by
    intro h0
    have := jfac_mul_conj g
    rw [h0, mul_zero] at this
    exact hn this.symm
  exact mul_right_cancel₀ hc key

private theorem W_eq_Wcl : W u₀ k₀ = Wcl u₀ k₀ := by
  funext g
  unfold W Wcl
  split_ifs with h
  · have hdet : g.det ≠ 0 := h.ne'
    have hn : 0 < nsq g := nsq_pos_of_det_ne_zero hdet
    have hj := jfac_ne_zero hdet
    set s : ℝ := Real.sqrt (nsq g) with hs_def
    have hs : 0 < s := Real.sqrt_pos.2 hn
    have hs2 : s ^ 2 = nsq g := Real.sq_sqrt hn.le
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'

    have hexp : Complex.exp (tpI * (nfac g / jfac g)) = psi (ix g) * (Real.exp (-(2 * Real.pi * iy g)) : ℂ) := by
      rw [nfac_div_jfac hdet, mul_add, Complex.exp_add, Complex.ofReal_exp]
      congr 1
      congr 1
      unfold tpI; push_cast
      have hI : I * I = -1 := I_mul_I
      linear_combination (2 * (Real.pi : ℂ) * (iy g : ℂ)) * hI

    have hinv : (jfac g)⁻¹ = ((g 1 1 : ℂ) - (g 1 0 : ℂ) * I) / (s : ℂ) ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hsC), inv_mul_eq_iff_eq_mul₀ hj, jfac_mul_conj]
      exact_mod_cast hs2

    have hiy : iy g ^ pexp k₀ = g.det ^ pexp k₀ / s ^ (k₀ + 2) := by
      have : iy g = g.det / s ^ 2 := by rw [iy, hs2]
      rw [this, Real.div_rpow h.le (sq_nonneg s)]
      congr 1
      rw [show (s ^ 2 : ℝ) = s ^ (2 : ℝ) from (Real.rpow_two s).symm, ← Real.rpow_mul hs.le,
        show (2 : ℝ) * pexp k₀ = ((k₀ + 2 : ℕ) : ℝ) by unfold pexp; push_cast; ring, Real.rpow_natCast]
    rw [hexp, prof, hiy, kap]
    rw [← hs_def]
    push_cast
    rw [div_eq_mul_inv (Kf u₀ k₀ g * _), ← inv_pow, hinv, Kf]
    rw [div_pow, div_pow]
    field_simp
    ring
  · rfl

end ClosedForm

section Flows

private theorem det_mul_flow (d : ArchDir) (x : M₂) (t : ℝ) : (x * (archFlowMatrix d t : M₂)).det = x.det := by
  rw [Matrix.det_mul]
  cases d <;> simp [archFlowMatrix, Matrix.det_fin_two_of, splitTorusGL2_coe, lowerUnipotentGL2_coe, ← Real.exp_add]

private theorem mul_flowE (x : M₂) (t : ℝ) :
    (x * (archFlowMatrix .E t : M₂)) 0 0 = x 0 0 ∧ (x * (archFlowMatrix .E t : M₂)) 0 1 = x 0 0 * t + x 0 1 ∧
    (x * (archFlowMatrix .E t : M₂)) 1 0 = x 1 0 ∧ (x * (archFlowMatrix .E t : M₂)) 1 1 = x 1 0 * t + x 1 1 := by
  simp [archFlowMatrix, Matrix.mul_apply, Fin.sum_univ_two]

private theorem mul_flowFm (x : M₂) (t : ℝ) :
    (x * (archFlowMatrix .Fm t : M₂)) 0 0 = x 0 0 + x 0 1 * t ∧ (x * (archFlowMatrix .Fm t : M₂)) 0 1 = x 0 1 ∧
    (x * (archFlowMatrix .Fm t : M₂)) 1 0 = x 1 0 + x 1 1 * t ∧ (x * (archFlowMatrix .Fm t : M₂)) 1 1 = x 1 1 := by
  simp [archFlowMatrix, lowerUnipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]

private theorem mul_flowH (x : M₂) (t : ℝ) :
    (x * (archFlowMatrix .H t : M₂)) 0 0 = x 0 0 * Real.exp t ∧
    (x * (archFlowMatrix .H t : M₂)) 0 1 = x 0 1 * Real.exp (-t) ∧
    (x * (archFlowMatrix .H t : M₂)) 1 0 = x 1 0 * Real.exp t ∧
    (x * (archFlowMatrix .H t : M₂)) 1 1 = x 1 1 * Real.exp (-t) := by
  simp [archFlowMatrix, splitTorusGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]

private theorem matrixFlowDeriv_eq_zero_of {F : M₂ → ℂ} (hF : ∀ y : M₂, ¬0 < y.det → F y = 0) {x : M₂}
    (hx : ¬0 < x.det) (d : ArchDir) : matrixFlowDeriv d F x = 0 := by
  unfold matrixFlowDeriv
  have : (fun t : ℝ => F (x * (archFlowMatrix d t : M₂))) = fun _ => 0 :=
    funext fun t => hF _ (by rwa [det_mul_flow])
  rw [this, deriv_const]

end Flows

section Derivatives

variable (u₀ : ℂ) (k₀ : ℕ)

private theorem
    Kf_mul_flow (d : ArchDir) (x : M₂) (t : ℝ) : Kf u₀ k₀ (x * (archFlowMatrix d t : M₂)) = Kf u₀ k₀ x := by
  simp only [Kf, detPow, det_mul_flow]

private def pE (x : M₂) : ℂ :=
  tpI * ((x 0 0 : ℂ) * jfac x - nfac x * (x 1 0 : ℂ)) - ((k₀ : ℂ) + 1) * (x 1 0 : ℂ) * jfac x

private def pFm (x : M₂) : ℂ :=
  tpI * ((x 0 1 : ℂ) * I * jfac x - nfac x * ((x 1 1 : ℂ) * I)) - ((k₀ : ℂ) + 1) * ((x 1 1 : ℂ) * I) * jfac x

private def pH (x : M₂) : ℂ :=
  tpI * (((x 0 0 : ℂ) * I - (x 0 1 : ℂ)) * jfac x - nfac x * ((x 1 0 : ℂ) * I - (x 1 1 : ℂ))) -
    ((k₀ : ℂ) + 1) * ((x 1 0 : ℂ) * I - (x 1 1 : ℂ)) * jfac x

private def GE (x : M₂) : ℂ :=
  if 0 < x.det then Kf u₀ k₀ x * Complex.exp (tpI * (nfac x / jfac x)) / jfac x ^ (k₀ + 2 + 1) * pE k₀ x else 0

private def GFm (x : M₂) : ℂ :=
  if 0 < x.det then Kf u₀ k₀ x * Complex.exp (tpI * (nfac x / jfac x)) / jfac x ^ (k₀ + 2 + 1) * pFm k₀ x else 0

private def GH (x : M₂) : ℂ :=
  if 0 < x.det then Kf u₀ k₀ x * Complex.exp (tpI * (nfac x / jfac x)) / jfac x ^ (k₀ + 2 + 1) * pH k₀ x else 0

private theorem Wcl_of_not {x : M₂} (hx : ¬0 < x.det) : Wcl u₀ k₀ x = 0 := by simp [Wcl, hx]

private theorem GE_of_not {x : M₂} (hx : ¬0 < x.det) : GE u₀ k₀ x = 0 := by simp [GE, hx]

private theorem GFm_of_not {x : M₂} (hx : ¬0 < x.det) : GFm u₀ k₀ x = 0 := by simp [GFm, hx]

private theorem GH_of_not {x : M₂} (hx : ¬0 < x.det) : GH u₀ k₀ x = 0 := by simp [GH, hx]

private theorem Wcl_flowE {x : M₂} (hx : 0 < x.det) (t : ℝ) :
    Wcl u₀ k₀ (x * (archFlowMatrix .E t : M₂)) =
      Kf u₀ k₀ x * Complex.exp (tpI * ((nfac x + (x 0 0 : ℂ) * (t : ℂ)) / (jfac x + (x 1 0 : ℂ) * (t : ℂ)))) *
        (1 + 0 * (t : ℂ) + 0 * (t : ℂ) ^ 2) / (jfac x + (x 1 0 : ℂ) * (t : ℂ)) ^ (k₀ + 1) := by
  obtain ⟨h00, h01, h10, h11⟩ := mul_flowE x t
  unfold Wcl
  rw [if_pos (by rwa [det_mul_flow]), Kf_mul_flow]
  simp only [nfac, jfac, h00, h01, h10, h11]
  push_cast
  ring_nf

private theorem Wcl_flowFm {x : M₂} (hx : 0 < x.det) (t : ℝ) :
    Wcl u₀ k₀ (x * (archFlowMatrix .Fm t : M₂)) =
      Kf u₀ k₀ x * Complex.exp (tpI * ((nfac x + (x 0 1 : ℂ) * I * (t : ℂ)) /
        (jfac x + (x 1 1 : ℂ) * I * (t : ℂ)))) *
        (1 + 0 * (t : ℂ) + 0 * (t : ℂ) ^ 2) / (jfac x + (x 1 1 : ℂ) * I * (t : ℂ)) ^ (k₀ + 1) := by
  obtain ⟨h00, h01, h10, h11⟩ := mul_flowFm x t
  unfold Wcl
  rw [if_pos (by rwa [det_mul_flow]), Kf_mul_flow]
  simp only [nfac, jfac, h00, h01, h10, h11]
  push_cast
  ring_nf

private theorem Wcl_flowH {x : M₂} (hx : 0 < x.det) (t : ℝ) :
    Wcl u₀ k₀ (x * (archFlowMatrix .H t : M₂)) =
      Kf u₀ k₀ x * Complex.exp (tpI * (((x 0 0 : ℂ) * I * (Real.exp t : ℂ) + (x 0 1 : ℂ) * (Real.exp (-t) : ℂ)) /
        ((x 1 0 : ℂ) * I * (Real.exp t : ℂ) + (x 1 1 : ℂ) * (Real.exp (-t) : ℂ)))) *
        (1 + 0 * (Real.exp t : ℂ) ^ 2 + 0 * (Real.exp (-t) : ℂ) ^ 2) /
          ((x 1 0 : ℂ) * I * (Real.exp t : ℂ) + (x 1 1 : ℂ) * (Real.exp (-t) : ℂ)) ^ (k₀ + 1) := by
  obtain ⟨h00, h01, h10, h11⟩ := mul_flowH x t
  unfold Wcl
  rw [if_pos (by rwa [det_mul_flow]), Kf_mul_flow]
  simp only [nfac, jfac, h00, h01, h10, h11]
  push_cast
  ring_nf

private theorem matrixFlowDeriv_E : matrixFlowDeriv .E (Wcl u₀ k₀) = GE u₀ k₀ := by
  funext x
  by_cases hx : 0 < x.det
  · have hj : jfac x ≠ 0 := jfac_ne_zero hx.ne'
    unfold matrixFlowDeriv
    rw [show (fun t : ℝ => Wcl u₀ k₀ (x * (archFlowMatrix .E t : M₂))) = _ from funext (Wcl_flowE u₀ k₀ hx),
      (FlowCore.hasDerivAt_affine (Kf u₀ k₀ x) tpI (nfac x) (jfac x) (x 0 0) (x 1 0) 1 0 0 k₀ hj).deriv, GE,
      if_pos hx, pE]
    ring
  · rw [GE_of_not u₀ k₀ hx]
    exact matrixFlowDeriv_eq_zero_of (fun y hy => Wcl_of_not u₀ k₀ hy) hx _

private theorem matrixFlowDeriv_Fm : matrixFlowDeriv .Fm (Wcl u₀ k₀) = GFm u₀ k₀ := by
  funext x
  by_cases hx : 0 < x.det
  · have hj : jfac x ≠ 0 := jfac_ne_zero hx.ne'
    unfold matrixFlowDeriv
    rw [show (fun t : ℝ => Wcl u₀ k₀ (x * (archFlowMatrix .Fm t : M₂))) = _ from funext (Wcl_flowFm u₀ k₀ hx),
      (FlowCore.hasDerivAt_affine (Kf u₀ k₀ x) tpI (nfac x) (jfac x) ((x 0 1 : ℂ) * I) ((x 1 1 : ℂ) * I) 1 0 0 k₀
        hj).deriv, GFm, if_pos hx, pFm]
    ring
  · rw [GFm_of_not u₀ k₀ hx]
    exact matrixFlowDeriv_eq_zero_of (fun y hy => Wcl_of_not u₀ k₀ hy) hx _

private theorem matrixFlowDeriv_H : matrixFlowDeriv .H (Wcl u₀ k₀) = GH u₀ k₀ := by
  funext x
  by_cases hx : 0 < x.det
  · have hj : jfac x ≠ 0 := jfac_ne_zero hx.ne'
    have hj' : (x 1 0 : ℂ) * I + (x 1 1 : ℂ) ≠ 0 := hj
    unfold matrixFlowDeriv
    rw [show (fun t : ℝ => Wcl u₀ k₀ (x * (archFlowMatrix .H t : M₂))) = _ from funext (Wcl_flowH u₀ k₀ hx),
      (FlowCore.hasDerivAt_expo (Kf u₀ k₀ x) tpI ((x 0 0 : ℂ) * I) (x 0 1) ((x 1 0 : ℂ) * I) (x 1 1) 1 0 0 k₀
        hj').deriv, GH, if_pos hx, pH, nfac, jfac]
    ring
  · rw [GH_of_not u₀ k₀ hx]
    exact matrixFlowDeriv_eq_zero_of (fun y hy => Wcl_of_not u₀ k₀ hy) hx _

private def qEFm (x : M₂) : ℂ :=
  tpI * ((x 0 0 : ℂ) * jfac x - nfac x * (x 1 0 : ℂ)) * pFm k₀ x +
    jfac x ^ 2 * (-(((k₀ : ℂ) + 1) * I * ((x 1 0 : ℂ) * (x 1 1 : ℂ) + (x 1 0 : ℂ) * jfac x))) -
      ((k₀ : ℂ) + 1 + 2) * (x 1 0 : ℂ) * jfac x * pFm k₀ x

private def qHH (x : M₂) : ℂ :=
  tpI * (((x 0 0 : ℂ) * I - (x 0 1 : ℂ)) * jfac x - nfac x * ((x 1 0 : ℂ) * I - (x 1 1 : ℂ))) * pH k₀ x +
    jfac x ^ 2 * (2 * (-(((k₀ : ℂ) + 1) * (x 1 0 : ℂ) ^ 2 * I ^ 2)) - 2 * (((k₀ : ℂ) + 1) * (x 1 1 : ℂ) ^ 2)) -
      ((k₀ : ℂ) + 1 + 2) * ((x 1 0 : ℂ) * I - (x 1 1 : ℂ)) * jfac x * pH k₀ x

private theorem GFm_flowE {x : M₂} (hx : 0 < x.det) (t : ℝ) :
    GFm u₀ k₀ (x * (archFlowMatrix .E t : M₂)) =
      Kf u₀ k₀ x * Complex.exp (tpI * ((nfac x + (x 0 0 : ℂ) * (t : ℂ)) / (jfac x + (x 1 0 : ℂ) * (t : ℂ)))) *
        (pFm k₀ x + -(((k₀ : ℂ) + 1) * I * ((x 1 0 : ℂ) * (x 1 1 : ℂ) + (x 1 0 : ℂ) * jfac x)) * (t : ℂ) +
          -(((k₀ : ℂ) + 1) * I * (x 1 0 : ℂ) ^ 2) * (t : ℂ) ^ 2) /
        (jfac x + (x 1 0 : ℂ) * (t : ℂ)) ^ (k₀ + 2 + 1) := by
  obtain ⟨h00, h01, h10, h11⟩ := mul_flowE x t
  unfold GFm
  rw [if_pos (by rwa [det_mul_flow]), Kf_mul_flow]
  simp only [pFm, nfac, jfac, h00, h01, h10, h11]
  push_cast
  ring_nf

private theorem GH_flowH {x : M₂} (hx : 0 < x.det) (t : ℝ) :
    GH u₀ k₀ (x * (archFlowMatrix .H t : M₂)) =
      Kf u₀ k₀ x * Complex.exp (tpI * (((x 0 0 : ℂ) * I * (Real.exp t : ℂ) + (x 0 1 : ℂ) * (Real.exp (-t) : ℂ)) /
        ((x 1 0 : ℂ) * I * (Real.exp t : ℂ) + (x 1 1 : ℂ) * (Real.exp (-t) : ℂ)))) *
        (tpI * (2 * (x 0 0 : ℂ) * (x 1 1 : ℂ) * I - 2 * (x 0 1 : ℂ) * (x 1 0 : ℂ) * I) +
          -(((k₀ : ℂ) + 1) * (x 1 0 : ℂ) ^ 2 * I ^ 2) * (Real.exp t : ℂ) ^ 2 +
            ((k₀ : ℂ) + 1) * (x 1 1 : ℂ) ^ 2 * (Real.exp (-t) : ℂ) ^ 2) /
          ((x 1 0 : ℂ) * I * (Real.exp t : ℂ) + (x 1 1 : ℂ) * (Real.exp (-t) : ℂ)) ^ (k₀ + 2 + 1) := by
  obtain ⟨h00, h01, h10, h11⟩ := mul_flowH x t
  unfold GH
  rw [if_pos (by rwa [det_mul_flow]), Kf_mul_flow]
  simp only [pH, nfac, jfac, h00, h01, h10, h11]
  have he0 : Complex.exp (t : ℂ) ≠ 0 := Complex.exp_ne_zero _
  push_cast
  rw [Complex.exp_neg]
  field_simp
  ring_nf

private theorem matrixFlowDeriv_E_GFm {x : M₂} (hx : 0 < x.det) :
    matrixFlowDeriv .E (GFm u₀ k₀) x =
      Kf u₀ k₀ x * Complex.exp (tpI * (nfac x / jfac x)) / jfac x ^ (k₀ + 4 + 1) * qEFm k₀ x := by
  have hj : jfac x ≠ 0 := jfac_ne_zero hx.ne'
  unfold matrixFlowDeriv
  rw [show (fun t : ℝ => GFm u₀ k₀ (x * (archFlowMatrix .E t : M₂))) = _ from funext (GFm_flowE u₀ k₀ hx),
    (FlowCore.hasDerivAt_affine (Kf u₀ k₀ x) tpI (nfac x) (jfac x) (x 0 0) (x 1 0) (pFm k₀ x) _ _ (k₀ + 2) hj).deriv,
    qEFm]
  push_cast
  ring

private theorem matrixFlowDeriv_H_GH {x : M₂} (hx : 0 < x.det) :
    matrixFlowDeriv .H (GH u₀ k₀) x =
      Kf u₀ k₀ x * Complex.exp (tpI * (nfac x / jfac x)) / jfac x ^ (k₀ + 4 + 1) * qHH k₀ x := by
  have hj : jfac x ≠ 0 := jfac_ne_zero hx.ne'
  have hj' : (x 1 0 : ℂ) * I + (x 1 1 : ℂ) ≠ 0 := hj
  unfold matrixFlowDeriv
  rw [show (fun t : ℝ => GH u₀ k₀ (x * (archFlowMatrix .H t : M₂))) = _ from funext (GH_flowH u₀ k₀ hx),
    (FlowCore.hasDerivAt_expo (Kf u₀ k₀ x) tpI ((x 0 0 : ℂ) * I) (x 0 1) ((x 1 0 : ℂ) * I) (x 1 1) _ _ _ (k₀ + 2)
      hj').deriv, qHH, pH, nfac, jfac]
  push_cast
  ring

end Derivatives

section Eigen

variable (u₀ : ℂ) (k₀ : ℕ)

private theorem matrixCasimir_Wcl {x : M₂} (hx : x.det ≠ 0) :
    matrixCasimir (Wcl u₀ k₀) x = (1 - (k₀ : ℂ) ^ 2) / 4 * Wcl u₀ k₀ x := by
  unfold matrixCasimir
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [matrixFlowDeriv_H, matrixFlowDeriv_Fm]
  by_cases hpos : 0 < x.det
  · have hj : jfac x ≠ 0 := jfac_ne_zero hx
    rw [matrixFlowDeriv_H_GH u₀ k₀ hpos, matrixFlowDeriv_E_GFm u₀ k₀ hpos, GH, if_pos hpos, Wcl, if_pos hpos]
    set C := Kf u₀ k₀ x * Complex.exp (tpI * (nfac x / jfac x)) with hC
    have e3 : C / jfac x ^ (k₀ + 2 + 1) = C / jfac x ^ (k₀ + 4 + 1) * jfac x ^ 2 := by
      field_simp; ring
    have e1 : C / jfac x ^ (k₀ + 1) = C / jfac x ^ (k₀ + 4 + 1) * jfac x ^ 4 := by
      field_simp; ring
    rw [e3, e1]
    have hid : -(1 / 4 * qHH k₀ x - 1 / 2 * (jfac x ^ 2 * pH k₀ x) + qEFm k₀ x) =
        (1 - (k₀ : ℂ) ^ 2) / 4 * jfac x ^ 4 := by
      simp only [qHH, qEFm, pH, pFm, nfac, jfac]
      ring
    linear_combination (C / jfac x ^ (k₀ + 4 + 1)) * hid
  · rw [matrixFlowDeriv_eq_zero_of (fun y hy => GH_of_not u₀ k₀ hy) hpos,
      matrixFlowDeriv_eq_zero_of (fun y hy => GFm_of_not u₀ k₀ hy) hpos, GH_of_not u₀ k₀ hpos,
      Wcl_of_not u₀ k₀ hpos]
    simp

private theorem matrixCasimir_W_eq {x : M₂} (hx : x.det ≠ 0) :
    matrixCasimir (W u₀ k₀) x = (1 - (k₀ : ℂ) ^ 2) / 4 * W u₀ k₀ x := by
  rw [W_eq_Wcl]; exact matrixCasimir_Wcl u₀ k₀ hx

end Eigen

end DiscreteFamily

end LanglandsTunnell.Converse

end
end

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_Converse_DiscreteFamily_matrixCasimir_W.LanglandsTunnell _root_.LanglandsTunnell.Converse _root_.P2MW.S_LanglandsTunnell_Converse_DiscreteFamily_matrixCasimir_W.LanglandsTunnell.Converse _root_.LanglandsTunnell.Converse.DiscreteFamily _root_.P2MW.S_LanglandsTunnell_Converse_DiscreteFamily_matrixCasimir_W.LanglandsTunnell.Converse.DiscreteFamily LanglandsTunnell.Converse.ArchCasimir in

theorem solution (u₀ : ℂ) (k₀ : ℕ) (hk : 1 ≤ k₀)
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) :
    matrixCasimir (DiscreteFamily.W u₀ k₀) x =
      (RealArchParam.discrete u₀ k₀ hk).laplaceEigenvalue * DiscreteFamily.W u₀ k₀ x :=
  by
    rw [RealArchParam.laplaceEigenvalue_discrete]
    exact DiscreteFamily.matrixCasimir_W_eq u₀ k₀ hx

end S_LanglandsTunnell_Converse_DiscreteFamily_matrixCasimir_W
end P2MW
export P2MW.S_LanglandsTunnell_Converse_DiscreteFamily_matrixCasimir_W (solution)
