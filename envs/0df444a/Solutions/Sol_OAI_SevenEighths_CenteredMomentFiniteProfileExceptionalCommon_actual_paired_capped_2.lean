-- Prove2me | solution 2 for OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalCommon.actual_paired_capped
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:34:38.439856+00:00
-- url     : https://prove2.me/submissions/c24666b4-a7e0-449d-8e28-d19a4068c7b5

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022
import Theorems.Thm_OAI_SevenEighths_CenteredMomentFiniteProfileExceptional_capped_rectangle_source_control
import Theorems.Thm_OAI_SevenEighths_CenteredMomentNaturalFixedRaySource_detector_capped_rectangle_uniform

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Mask
namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentMask
open ActualEisensteinCubic IdealMobiusDivisorSum
open UniqueFactorizationMonoid

theorem tsum_ideal_divisible (D : Ideal O) (hD : D ≠ 0) (f : Ideal O → ℂ) :
    (∑' I : Ideal O, if D ∣ I then f I else 0) =
      ∑' J : Ideal O, f (D * J) := by
  let F : Ideal O → ℂ := fun I => if D ∣ I then f I else 0
  have hrange : Function.support F ⊆ Set.range (fun J : Ideal O => D * J) := by
    intro I hI
    have hd : D ∣ I := by
      by_contra hn
      exact hI (by simp only [F, if_neg hn])
    obtain ⟨J, hJ⟩ := hd
    exact ⟨J, hJ.symm⟩
  have ht := (mul_right_injective₀ hD).tsum_eq hrange
  calc
    _ = ∑' J : Ideal O, F (D * J) := ht.symm
    _ = _ := by
      apply tsum_congr
      intro J
      simp only [F, dvd_mul_right, ite_true]

theorem annular_ideal_sum_summable (χ : Ideal O → ℂ) (W : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hs : Function.support W ⊆ Set.Iic b) :
    Summable (fun I : Ideal O => χ I * W ((Ideal.absNorm I : ℝ) / X)) := by
  apply summable_of_hasFiniteSupport
  apply (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil (b * X))).subset
  intro I hI
  have hw : W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
    intro hz
    exact hI (by simp only [hz, mul_zero])
  have hn : (Ideal.absNorm I : ℝ) ≤ b * X := (div_le_iff₀ hX).mp (hs hw)
  exact_mod_cast hn.trans (Nat.le_ceil (b * X))

end SevenEighths.CenteredMomentMask
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Counting
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCounting
open CenteredMomentPrimary
open QuadraticInitialBound

theorem norm_tsum_ideal_ball (f : Ideal O → ℂ) (H M : ℝ)
    (hH : 0 ≤ H) (hM : 0 ≤ M) (hzero : f ⊥ = 0)
    (hbound : ∀ I, ‖f I‖ ≤ M)
    (hsupport : ∀ I, f I ≠ 0 → (Ideal.absNorm I : ℝ) ≤ H) :
    ‖∑' I : Ideal O, f I‖ ≤ 128 * M * H := by
  classical
  have hfinite : (Function.support f).Finite := by
    apply (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil H)).subset
    intro I hI
    exact_mod_cast (hsupport I hI).trans (Nat.le_ceil H)
  let S := hfinite.toFinset
  have hmem (I : Ideal O) : I ∈ S ↔ f I ≠ 0 := hfinite.mem_toFinset
  have htsum : (∑' I : Ideal O, f I) = ∑ I ∈ S, f I := by
    exact tsum_eq_sum (fun I hI => not_ne_iff.mp (mt (hmem I).mpr hI))
  rw [htsum]
  by_cases hS : S.Nonempty
  · obtain ⟨I, hI⟩ := hS
    have hI0 : I ≠ ⊥ := by intro h; exact (hmem I).mp hI (h ▸ hzero)
    have hn : 1 ≤ (Ideal.absNorm I : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (fun hz => hI0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hH1 : 1 ≤ H := hn.trans (hsupport I ((hmem I).mp hI))
    have hcount := DescentFiberCost.finite_ideal_count_real S H hH1
      (fun J hJ hz => (hmem J).mp hJ (hz ▸ hzero))
      (fun J hJ => hsupport J ((hmem J).mp hJ))
    calc
      _ ≤ ∑ I ∈ S, ‖f I‖ := norm_sum_le _ _
      _ ≤ ∑ _I ∈ S, M := Finset.sum_le_sum (fun I _ => hbound I)
      _ = (S.card : ℝ) * M := by simp
      _ ≤ (128 * H) * M := mul_le_mul_of_nonneg_right hcount hM
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp only [Finset.sum_empty, norm_zero]
    positivity

end SevenEighths.CenteredMomentCounting
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Twist
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentTwist
open ActualEisensteinCubic EisensteinSchwartzPoisson
open CenteredMomentLattice CenteredMomentCounting

lemma norm_real_imaginary_power (X t : ℝ) (hX : 0 < X) :
    ‖(X : ℂ) ^ (Complex.I * t)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp

end SevenEighths.CenteredMomentTwist
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Extraction
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentExtraction
open CenteredMomentRectangle CenteredMomentPrimary CenteredMomentTwist

theorem idealRectangle_extract (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ I J : Ideal O) :
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J) =
      idealRectangle W₁ W₂
        (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
        (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂) I J := by
  simp only [idealRectangle, map_mul, Nat.cast_mul, div_div_eq_mul_div]
  congr 2 <;> congr 1 <;> ring

end SevenEighths.CenteredMomentExtraction
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.HeckeSlots
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeSlots
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentCounting CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

theorem row_twisted_coefficient_norm (η : Character) (m A z : O) (t : ℝ)
    (P : Ideal O) (hP : P ≠ 0) :
    ‖(idealCoeff η P * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) P) *
      (Ideal.absNorm P:ℂ)^(Complex.I*t)‖ ≤ 1 := by
  have hn : 0 < (Ideal.absNorm P:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP)
  rw [norm_mul, norm_mul, show (Ideal.absNorm P:ℂ)=((Ideal.absNorm P:ℝ):ℂ) by simp,
    norm_real_imaginary_power _ t hn, mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η P)).trans
    (CanonicalRowCompletion.idealRowHom_norm _ _)

theorem rowSlot_bound (η : Character) (m A z : O) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t H M : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hβ : ∀ P ∈ S, ‖β P‖ ≤ M)
    (hN : ∀ P ∈ S, β P ≠ 0 → (Ideal.absNorm P:ℝ) ≤ H) :
    ‖rowSlot η m A z S β t‖ ≤ 128*M*H := by
  let f : Ideal O → ℂ := fun P => if P ∈ S then
    β P * (idealCoeff η P * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) P) *
      (Ideal.absNorm P:ℂ)^(Complex.I*t) else 0
  have hf0 : f 0=0 := by simp only [f, map_zero, zero_mul, mul_zero, ite_self]
  have hf : ∀ P, ‖f P‖ ≤ M := by
    intro P
    by_cases hP : P ∈ S
    · by_cases hP0 : P=0
      · rw [hP0,hf0,norm_zero]; exact hM
      · dsimp only [f]; rw [if_pos hP, mul_assoc, norm_mul]
        exact (mul_le_mul (hβ P hP) (row_twisted_coefficient_norm η m A z t P hP0)
          (norm_nonneg _) hM).trans_eq (mul_one M)
    · simp only [f,if_neg hP,norm_zero]; exact hM
  have hsup : ∀ P, f P ≠ 0 → (Ideal.absNorm P:ℝ) ≤ H := by
    intro P hP
    have hm : P ∈ S := by by_contra hn; exact hP (by simp only [f,if_neg hn])
    exact hN P hm (by intro hz; exact hP (by simp only [f,if_pos hm,hz,zero_mul]))
  have he : (∑' P, f P)=rowSlot η m A z S β t := by
    rw [tsum_eq_sum (s := S) (fun P hP => by simp only [f,if_neg hP])]
    unfold rowSlot
    exact Finset.sum_congr rfl (fun P hP => by simp only [f,if_pos hP])
  rw [← he]
  exact norm_tsum_ideal_ball f H M hH hM hf0 hf hsup

variable {ι : Type*} [Fintype ι]

theorem whole_product_normalization (R : ℂ) (q : ι → ℂ) (k p : ι → ℝ)
    (D T L : ℝ) (hD : 0 ≤ D) (hT : 0 < T) (hL : 0 < L)
    (_hk : ∀ i, 0 ≤ k i) (hp : ∀ i, 0 < p i)
    (hq : ∀ i, ‖q i‖ ≤ k i*p i)
    (hR : ‖(Real.sqrt T:ℂ)⁻¹*R‖ ≤ D*(Real.sqrt T/L)) :
    ‖(Real.sqrt (T*∏ i,p i):ℂ)⁻¹*(R*∏ i,q i)‖ ≤
      D*(∏ i,k i)*(Real.sqrt (T*∏ i,p i)/L) := by
  have hP : 0 < ∏ i,p i := Finset.prod_pos (fun i _ => hp i)
  have hTP : 0 < T*∏ i,p i := mul_pos hT hP
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hsTP : 0 < Real.sqrt (T*∏ i,p i) := Real.sqrt_pos.2 hTP
  have hQ : ‖∏ i,q i‖ ≤ (∏ i,k i)*(∏ i,p i) := by
    rw [norm_prod,← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hq i)
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hsT.le] at hR
  have hR' : ‖R‖ ≤ D*T/L := by
    have h := mul_le_mul_of_nonneg_left hR hsT.le
    rw [← mul_assoc,mul_inv_cancel₀ hsT.ne',one_mul] at h
    have hs := Real.sq_sqrt hT.le
    convert (preTransparency := .instances) h using 1
    calc
      D*T/L = D*(Real.sqrt T)^2/L := by rw [hs]
      _ = _ := by ring
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hsTP.le,norm_mul]
  calc
    _ ≤ (Real.sqrt (T*∏ i,p i))⁻¹*((D*T/L)*((∏ i,k i)*(∏ i,p i))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hR' hQ (norm_nonneg _) (by positivity)) (inv_nonneg.mpr hsTP.le)
    _ = _ := by
      have hs := Real.sq_sqrt hTP.le
      field_simp
      rw [hs]

end SevenEighths.CenteredMomentHeckeSlots

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.HeckeExpansion
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeExpansion
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRectangle CenteredMomentPrimary CenteredMomentTwist CenteredMomentMask
local notation "O" => ActualEisensteinCubic.O

theorem rowTwistedSum_eq_weight (η : Character) (m A z : O) (t : ℝ) (W : ℝ → ℂ) (X : ℝ) :
    rowTwistedSum η m A z W t X =
      ∑' I : Ideal O, rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X) := rfl

theorem rowSlot_eq_weight (η : Character) (m A z : O) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t : ℝ) :
    rowSlot η m A z S β t = ∑ P ∈ S, β P*rowWeight η m A z t P := by
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro P hP
  simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk]
  ring

theorem actual_hecke_rectangle_sum
    (η : Character) (m A z : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑' I : Ideal O, ∑' J : Ideal O,
      rowWeight η m A z t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      rowTwistedSum η m A z W₁ t X₁ * rowTwistedSum η m A z W₂ t X₂ -
        rowTwistedSum η m A z W₁ t Y₁ * rowTwistedSum η m A z W₂ t Y₂ := by
  let w := rowWeight η m A z t
  let f₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / X₁)
  let f₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / X₂)
  let g₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / Y₁)
  let g₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / Y₂)
  have hf₁ : Summable f₁ := annular_ideal_sum_summable w W₁ b₁ X₁ hX₁ hs₁
  have hf₂ : Summable f₂ := annular_ideal_sum_summable w W₂ b₂ X₂ hX₂ hs₂
  have hg₁ : Summable g₁ := annular_ideal_sum_summable w W₁ b₁ Y₁ hY₁ hs₁
  have hg₂ : Summable g₂ := annular_ideal_sum_summable w W₂ b₂ Y₂ hY₂ hs₂
  have hterm (I J : Ideal O) :
      rowWeight η m A z t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        f₁ I * f₂ J - g₁ I * g₂ J := by
    rw [map_mul]
    dsimp only [idealRectangle, f₁, f₂, g₁, g₂, w]
    ring
  simp_rw [hterm]
  have hinner (I : Ideal O) : (∑' J : Ideal O, (f₁ I * f₂ J - g₁ I * g₂ J)) =
      f₁ I * (∑' J : Ideal O, f₂ J) - g₁ I * (∑' J : Ideal O, g₂ J) := by
    rw [Summable.tsum_sub (hf₂.mul_left _) (hg₂.mul_left _), tsum_mul_left, tsum_mul_left]
  simp_rw [hinner]
  rw [Summable.tsum_sub (hf₁.mul_right _) (hg₁.mul_right _), tsum_mul_right, tsum_mul_right]
  simp only [rowTwistedSum_eq_weight]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem live_slot_product (η : Character) (m A z : O) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (t : ℝ) :
    (∏ i,rowSlot η m A z (S i) (β i) t) =
      ∑ v : (i : ι) → S i, (∏ i,β i (v i))*rowWeight η m A z t (∏ i,(v i:Ideal O)) := by
  have hs (i : ι) : rowSlot η m A z (S i) (β i) t =
      ∑ P : S i, β i P*rowWeight η m A z t P := by
    rw [rowSlot_eq_weight]
    exact (Finset.sum_coe_sort (S i) (fun P => β i P*rowWeight η m A z t P)).symm
  simp_rw [hs]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [map_prod,← Finset.prod_mul_distrib]

theorem actual_slot_rectangle_sum (η : Character) (m A z : O)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑ v : (i : ι) → S i, (∏ i,β i (v i))*
      ∑' I : Ideal O, ∑' J : Ideal O,
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
       rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)*
       ∏ i,rowSlot η m A z (S i) (β i) t := by
  have ht (v : (i : ι) → S i) (I J : Ideal O) :
      rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        rowWeight η m A z t (∏ i,(v i:Ideal O))*
          (rowWeight η m A z t (I*J)*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) := by
    simp only [map_mul]; ring
  simp_rw [ht,tsum_mul_left]
  rw [actual_hecke_rectangle_sum η m A z t W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂,
    live_slot_product]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem common_extracted_slot_rectangle (η : Character) (m A z : O)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (∑ v : (i : ι) → S i, (∏ i,β i (v i))*
      ∑' I : Ideal O, ∑' J : Ideal O,
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*(B₁*I)*(B₂*J))*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)) =
      rowWeight η m A z t (B₁*B₂)*
        ∑ v : (i : ι) → S i, (∏ i,β i (v i))*
          ∑' I : Ideal O, ∑' J : Ideal O,
            rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
              idealRectangle W₁ W₂ (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
                (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) I J := by
  have ht (v : (i : ι) → S i) (I J : Ideal O) :
      rowWeight η m A z t ((∏ i,(v i:Ideal O))*(B₁*I)*(B₂*J))*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J) =
      rowWeight η m A z t (B₁*B₂)*
        (rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
            (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) I J) := by
    rw [CenteredMomentExtraction.idealRectangle_extract]
    simp only [map_mul]
    ring
  simp_rw [ht,tsum_mul_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

end SevenEighths.CenteredMomentHeckeExpansion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorExtraction
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorExtraction
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem selected_divides_factor (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0)
    (P : primeSupport D) (i : ι) (hi : i ∈ (a P).val) : (P:Ideal O)∣v i := by
  have hP := (Finset.prod_ne_zero_iff.mp hn) P (Finset.mem_univ P)
  have hprod := (mul_ne_zero_iff.mp hP).2
  have hfactor := (Finset.prod_ne_zero_iff.mp hprod) i hi
  by_contra h
  exact hfactor (by simp only [if_neg h])

theorem selectedDivisor_dvd (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0) (i : ι) :
    selectedDivisor D s a i ∣ v i := by
  apply Finset.prod_dvd_of_coprime ?_ ?_
  · intro P hP Q hQ hne
    let : (P:Ideal O).IsMaximal := (Ideal.isPrime_of_prime (support_prime P.property)).isMaximal
      (support_prime P.property).ne_zero
    let : (Q:Ideal O).IsMaximal := (Ideal.isPrime_of_prime (support_prime Q.property)).isMaximal
      (support_prime Q.property).ne_zero
    exact Ideal.isCoprime_of_isMaximal (fun he => hne (Subtype.ext he))
  · intro P hP
    exact selected_divides_factor D s v a hn P i (Finset.mem_filter.mp hP).2

end SevenEighths.CenteredMomentDivisorExtraction

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorTensor
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorTensor
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentMask HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem allocationSign_norm (D : Ideal O) (s : Finset ι) (a : Allocation D s) :
    ‖allocationSign D s a‖=1 := by
  simp only [allocationSign,norm_prod,norm_pow,norm_neg,norm_one,one_pow,Finset.prod_const_one]

theorem allocationTerm_eq_ite (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) :
    allocationTerm D s v a =
      if ∀ i ∈ s, selectedDivisor D s a i∣v i then allocationSign D s a else 0 := by
  by_cases hh : ∀ i ∈ s, selectedDivisor D s a i∣v i
  · rw [if_pos hh]
    unfold allocationTerm allocationSign
    apply Finset.prod_congr rfl
    intro P hP
    have he : (∏ i ∈ (a P).val,if (P:Ideal O)∣v i then (1:ℂ) else 0)=1 := by
      apply Finset.prod_eq_one
      intro i hi
      have his : i ∈ s := (Finset.mem_powerset.mp (Finset.mem_of_mem_erase (a P).property)) hi
      have hPi : (P:Ideal O)∣selectedDivisor D s a i :=
        Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ P,hi⟩)
      rw [if_pos (hPi.trans (hh i his))]
    rw [he,mul_one]
  · rw [if_neg hh]
    by_contra hn
    exact hh (fun i _ => selectedDivisor_dvd D s v a hn i)

theorem allocationTerm_eq_product (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) :
    allocationTerm D s v a = allocationSign D s a*
      ∏ i ∈ s, if selectedDivisor D s a i∣v i then (1:ℂ) else 0 := by
  rw [allocationTerm_eq_ite]
  by_cases hh : ∀ i ∈ s, selectedDivisor D s a i∣v i
  · rw [if_pos hh,Finset.prod_eq_one (fun i hi => by rw [if_pos (hh i hi)]),mul_one]
  · rw [if_neg hh]
    push Not at hh
    obtain ⟨i,hi,hnd⟩ := hh
    rw [Finset.prod_eq_zero hi (by simp only [if_neg hnd]),mul_zero]

end SevenEighths.CenteredMomentDivisorTensor

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorSlots
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorSlots
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem selected_slot_exact (η : Character) (m A z : O) (t : ℝ)
    (D P : Ideal O) (hP : Prime P) (hPD : P∣D)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I) (β : Ideal O → ℂ) :
    rowSlot η m A z S (fun I => if D∣I then β I else 0) t =
      if P ∈ S ∧ D∣P then β P*rowWeight η m A z t P else 0 := by
  rw [rowSlot_eq_weight]
  have hz (I : Ideal O) (hI : I ∈ S) (hne : I ≠ P) :
      (if D∣I then β I else 0)*rowWeight η m A z t I=0 := by
    have hnd : ¬D∣I := fun hd => hne ((prime_dvd_prime_iff_eq hP (hS I hI)).mp (hPD.trans hd)).symm
    simp only [if_neg hnd,zero_mul]
  by_cases hmem : P ∈ S
  · rw [Finset.sum_eq_single P (fun I hI hne => hz I hI hne) (fun h => (h hmem).elim)]
    by_cases hd : D∣P <;> simp only [hmem,hd,and_self,true_and,ite_true,ite_false,zero_mul]
  · rw [Finset.sum_eq_zero (fun I hI => hz I hI (fun he => hmem (he ▸ hI)))]
    simp only [hmem,false_and,ite_false]

theorem selected_slot_bound (η : Character) (m A z : O) (t : ℝ)
    (D P : Ideal O) (hP : Prime P) (hPD : P∣D)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I)
    (β : Ideal O → ℂ) (M : ℝ) (hM : 0 ≤ M) (hβ : ∀ I ∈ S, ‖β I‖ ≤ M) :
    ‖rowSlot η m A z S (fun I => if D∣I then β I else 0) t‖ ≤ M := by
  rw [selected_slot_exact η m A z t D P hP hPD S hS β]
  split_ifs with h
  · rw [norm_mul]
    exact (mul_le_mul (hβ P h.1) (row_twisted_coefficient_norm η m A z t P hP.ne_zero)
      (norm_nonneg _) hM).trans_eq (mul_one M)
  · simpa only [norm_zero] using hM

theorem selectedDivisor_empty (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι)
    (he : selectedPrimes D s a i=∅) : selectedDivisor D s a i=1 := by
  simp only [selectedDivisor,he,Finset.prod_empty]

end SevenEighths.CenteredMomentDivisorSlots

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorRectangle
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorRectangle
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorTensor
open CenteredMomentHeckeExpansion CenteredMomentMask CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem allocationTerm_rectangle (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (I J : Ideal O) :
    allocationTerm D Finset.univ (factorTuple v I J) a =
      allocationSign D Finset.univ a *
        (∏ i,if selectedSlot D a i ∣ v i then (1:ℂ) else 0)*
        (if selectedPlain D a 0 ∣ I then 1 else 0)*
        (if selectedPlain D a 1 ∣ J then 1 else 0) := by
  rw [allocationTerm_eq_product,Fintype.prod_sum_type,Fin.prod_univ_two]
  simp only [factorTuple,Sum.elim_inl,Sum.elim_inr,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false,
    selectedPlain,selectedSlot]
  simp only [mul_assoc]
  rfl

theorem double_selected_reindex (D₁ D₂ : Ideal O) (h₁ : D₁ ≠ 0) (h₂ : D₂ ≠ 0)
    (F : Ideal O → Ideal O → ℂ) :
    (∑' I : Ideal O,∑' J : Ideal O,
      (if D₁∣I then (1:ℂ) else 0)*(if D₂∣J then 1 else 0)*F I J) =
      ∑' I : Ideal O,∑' J : Ideal O,F (D₁*I) (D₂*J) := by
  have he (I J : Ideal O) :
      (if D₁∣I then (1:ℂ) else 0)*(if D₂∣J then 1 else 0)*F I J =
        if D₁∣I then (if D₂∣J then F I J else 0) else 0 := by
    split_ifs <;> simp
  simp_rw [he]
  have hi (I : Ideal O) :
      (∑' J : Ideal O,if D₁∣I then (if D₂∣J then F I J else 0) else 0) =
        if D₁∣I then (∑' J : Ideal O,if D₂∣J then F I J else 0) else 0 := by
    split_ifs <;> simp
  simp_rw [hi]
  rw [tsum_ideal_divisible D₁ h₁]
  exact tsum_congr (fun I => tsum_ideal_divisible D₂ h₂ (F (D₁*I)))

theorem allocated_rectangle_reindex (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∑ v : (i : ι) → S i,(∏ i,β i (v i))*
      ∑' I : Ideal O,∑' J : Ideal O,
        allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      allocationSign D Finset.univ a *
        rowWeight η m A z t (selectedPlain D a 0*selectedPlain D a 1)*
        ∑ v : (i : ι) → S i,
          (∏ i,if selectedSlot D a i ∣ (v i:Ideal O) then β i (v i) else 0)*
          ∑' I : Ideal O,∑' J : Ideal O,
            rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
            idealRectangle W₁ W₂
              (X₁/Ideal.absNorm (selectedPlain D a 0)) (X₂/Ideal.absNorm (selectedPlain D a 1))
              (Y₁/Ideal.absNorm (selectedPlain D a 0)) (Y₂/Ideal.absNorm (selectedPlain D a 1)) I J := by
  let F (v : (i : ι) → S i) (I J : Ideal O) :=
    rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J
  have he (v : (i : ι) → S i) (I J : Ideal O) :
      allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
      (allocationSign D Finset.univ a * (∏ i,if selectedSlot D a i∣(v i:Ideal O) then (1:ℂ) else 0))*
        ((if selectedPlain D a 0∣I then (1:ℂ) else 0)*
          (if selectedPlain D a 1∣J then 1 else 0)*F v I J) := by
    rw [allocationTerm_rectangle]
    dsimp only [F]
    ring
  have hint (v : (i : ι) → S i) :
      (∑' I : Ideal O,∑' J : Ideal O,
        allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      (allocationSign D Finset.univ a * (∏ i,if selectedSlot D a i∣(v i:Ideal O) then (1:ℂ) else 0))*
        (∑' I : Ideal O,∑' J : Ideal O,F v (selectedPlain D a 0*I) (selectedPlain D a 1*J)) := by
    simp_rw [he]
    have ht := double_selected_reindex (selectedPlain D a 0) (selectedPlain D a 1)
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 0))
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 1)) (F v)
    rw [← ht,← tsum_mul_left]
    apply tsum_congr
    intro I
    exact tsum_mul_left
  simp_rw [hint]
  have hβ (v : (i : ι) → S i) :
      (∏ i,β i (v i))*(allocationSign D Finset.univ a*
        (∏ i,if selectedSlot D a i∣(v i:Ideal O) then (1:ℂ) else 0)) =
      allocationSign D Finset.univ a *
        (∏ i,if selectedSlot D a i∣(v i:Ideal O) then β i (v i) else 0) := by
    rw [mul_left_comm,← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    split_ifs <;> simp
  simp_rw [← mul_assoc]
  simp only [← mul_assoc] at hβ
  simp_rw [hβ]
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  dsimp only [F]
  rw [common_extracted_slot_rectangle η m A z S
    (fun i I => if selectedSlot D a i∣I then β i I else 0) t
    W₁ W₂ X₁ X₂ Y₁ Y₂ (selectedPlain D a 0) (selectedPlain D a 1)]
  simp only [mul_assoc]

end SevenEighths.CenteredMomentDivisorRectangle

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorRows
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRows
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorTensor
open CenteredMomentDivisorRectangle CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
open CenteredMomentHeckeSlots CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem allocatedRectangle_eq_rows (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ =
      allocationSign D Finset.univ a *
        rowWeight η m A z t (selectedPlain D a 0*selectedPlain D a 1)*
        ((rowTwistedSum η m A z W₁ t (X₁/Ideal.absNorm (selectedPlain D a 0))*
          rowTwistedSum η m A z W₂ t (X₂/Ideal.absNorm (selectedPlain D a 1))-
          rowTwistedSum η m A z W₁ t (Y₁/Ideal.absNorm (selectedPlain D a 0))*
          rowTwistedSum η m A z W₂ t (Y₂/Ideal.absNorm (selectedPlain D a 1)))*
          ∏ i,rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t) := by
  have hN (j : Fin 2) : (0:ℝ) < Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  unfold allocatedRectangle
  rw [allocated_rectangle_reindex]
  rw [actual_slot_rectangle_sum η m A z S
    (fun i I => if selectedSlot D a i∣I then β i I else 0) t W₁ W₂ b₁ b₂
    _ _ _ _ hW₁ hW₂ (div_pos hX₁ (hN 0)) (div_pos hX₂ (hN 1))
    (div_pos hY₁ (hN 0)) (div_pos hY₂ (hN 1))]

theorem allocatedRectangle_norm_le (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖ ≤
      ‖rowTwistedSum η m A z W₁ t (X₁/Ideal.absNorm (selectedPlain D a 0))*
        rowTwistedSum η m A z W₂ t (X₂/Ideal.absNorm (selectedPlain D a 1))-
        rowTwistedSum η m A z W₁ t (Y₁/Ideal.absNorm (selectedPlain D a 0))*
        rowTwistedSum η m A z W₂ t (Y₂/Ideal.absNorm (selectedPlain D a 1))‖ *
        ∏ i,‖rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t‖ := by
  rw [allocatedRectangle_eq_rows η m A z t S β D a W₁ W₂ b₁ b₂ _ _ _ _
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂,norm_mul,norm_mul,allocationSign_norm,one_mul,norm_mul,norm_prod]
  apply mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  exact row_twisted_coefficient_norm η m A z t _ (mul_ne_zero
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 0))
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 1)))

end SevenEighths.CenteredMomentDivisorRows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorRaw
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorSlots
open CenteredMomentDivisorRectangle CenteredMomentDivisorRows CenteredMomentHeckeExpansion
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem split_slot_product {M : Type*} [CommMonoid M] (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (f : ι → M) :
    (∏ i∈frozenIndices D a,f i)*(∏ i∈liveIndices D a,f i)=∏ i,f i :=
  Finset.prod_filter_mul_prod_filter_not _ _ _

theorem selected_live_slot (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (i : ι) (hi : i ∈ liveIndices D a) (S : Finset (Ideal O)) (β : Ideal O → ℂ) :
    rowSlot η m A z S (fun I => if selectedSlot D a i∣I then β I else 0) t =
      rowSlot η m A z S β t := by
  have he := selectedDivisor_empty D Finset.univ a (Sum.inl i)
    (Finset.not_nonempty_iff_eq_empty.mp (Finset.mem_filter.mp hi).2)
  simp only [selectedSlot,he,one_dvd,ite_true]

theorem selected_frozen_slot_bound (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (i : ι) (hi : i ∈ frozenIndices D a) (S : Finset (Ideal O))
    (hS : ∀ I∈S,Prime I) (β : Ideal O → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hβ : ∀ I∈S,‖β I‖ ≤ M) :
    ‖rowSlot η m A z S (fun I => if selectedSlot D a i∣I then β I else 0) t‖ ≤ M := by
  obtain ⟨P,hP⟩ := (Finset.mem_filter.mp hi).2
  exact selected_slot_bound η m A z t (selectedSlot D a i) P
    (IdealMobiusDivisorSum.support_prime P.property) (Finset.dvd_prod_of_mem _ hP)
    S hS β M hM hβ

theorem selected_slot_product_bound (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (M : ι → ℝ) (hM : ∀ i,0 ≤ M i)
    (hβ : ∀ i,∀ I∈S i,‖β i I‖ ≤ M i) :
    (∏ i,‖rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t‖) ≤
      (∏ i∈frozenIndices D a,M i)*∏ i∈liveIndices D a,‖rowSlot η m A z (S i) (β i) t‖ := by
  rw [← split_slot_product D a]
  apply mul_le_mul
  · apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro i hi
    exact selected_frozen_slot_bound η m A z t D a i hi (S i) (hS i) (β i) (M i) (hM i) (hβ i)
  · apply le_of_eq
    apply Finset.prod_congr rfl
    intro i hi
    rw [selected_live_slot η m A z t D a i hi]
  · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  · exact Finset.prod_nonneg (fun i _ => hM i)

theorem selectedNorm_pos (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) :
    0 < selectedNorm D a := by
  apply mul_pos <;> exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (selectedDivisor_ne_zero D Finset.univ a _))

theorem raw_scale_identity (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (T : ℝ) (P : ι → ℝ) :
    rawRemaining D a T P*formalReductionFactor D a P=T*∏ i,P i := by
  unfold rawRemaining formalReductionFactor
  rw [← split_slot_product D a P]
  field_simp [(selectedNorm_pos D a).ne']

end SevenEighths.CenteredMomentDivisorRaw

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorRawEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorRows
open CenteredMomentDivisorRaw CenteredMomentHeckeSlots CenteredMomentHeckeHeight HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem normalized_norm_sq (T : ℝ) (hT : 0 < T) (x : ℂ) :
    ‖(Real.sqrt T:ℂ)⁻¹*x‖^2=‖x‖^2/T := by
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,inv_pow,
    Real.sq_sqrt hT.le]
  ring

theorem allocated_raw_energy (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (M P : ι → ℝ) (hM : ∀ i,0 ≤ M i) (hP : ∀ i,0 < P i)
    (hβ : ∀ i,∀ I∈S i,‖β i I‖ ≤ M i)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hT : 0 < T) :
    ‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 ≤
      (∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P *
        ‖residualCenteredRow η m A z t S β P D a W₁ W₂ X₁ X₂ Y₁ Y₂ T‖^2 := by
  let R : ℂ :=
    rowTwistedSum η m A z W₁ t (X₁/Ideal.absNorm (selectedPlain D a 0))*
      rowTwistedSum η m A z W₂ t (X₂/Ideal.absNorm (selectedPlain D a 1))-
    rowTwistedSum η m A z W₁ t (Y₁/Ideal.absNorm (selectedPlain D a 0))*
      rowTwistedSum η m A z W₂ t (Y₂/Ideal.absNorm (selectedPlain D a 1))
  let L : ℂ := R*∏ i∈liveIndices D a,rowSlot η m A z (S i) (β i) t
  have hn : ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖ ≤
      (∏ i∈frozenIndices D a,M i)*‖L‖ := by
    apply (allocatedRectangle_norm_le η m A z t S β D a W₁ W₂ b₁ b₂
      _ _ _ _ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂).trans
    have hh := mul_le_mul_of_nonneg_left
      (selected_slot_product_bound η m A z t D a S hS β M hM hβ) (norm_nonneg R)
    dsimp only [L]
    rw [norm_mul,norm_prod]
    convert (preTransparency := .instances) hh using 1 ; ring
  have hraw : 0 < rawRemaining D a T P := mul_pos (div_pos hT (selectedNorm_pos D a))
    (Finset.prod_pos (fun i _ => hP i))
  have hformal : 0 < formalReductionFactor D a P := mul_pos (selectedNorm_pos D a)
    (Finset.prod_pos (fun i _ => hP i))
  have htotal : 0 < T*∏ i,P i := mul_pos hT (Finset.prod_pos (fun i _ => hP i))
  have hres : ‖residualCenteredRow η m A z t S β P D a W₁ W₂ X₁ X₂ Y₁ Y₂ T‖^2 =
      ‖L‖^2/rawRemaining D a T P := by
    unfold residualCenteredRow centeredSlotRow
    rw [Finset.prod_coe_sort (liveIndices D a) P,
      Finset.prod_coe_sort (liveIndices D a) (fun i => rowSlot η m A z (S i) (β i) t)]
    exact normalized_norm_sq _ hraw L
  rw [normalized_norm_sq _ htotal,hres]
  calc
    _ ≤ ((∏ i∈frozenIndices D a,M i)*‖L‖)^2/(T*∏ i,P i) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn 2) htotal.le
    _ = _ := by
      rw [← raw_scale_identity D a T P,mul_pow]
      field_simp [hraw.ne',hformal.ne']

end SevenEighths.CenteredMomentDivisorRawEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ExceptionalCappedAmplitude
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentExceptionalCappedAmplitude
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentCounting CenteredMomentHeckeTwist CenteredMomentTwist CenteredMomentLattice
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCanonicalFirst
open CenteredMomentForcing CenteredMomentChildRows
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
local notation "O" => HeckeFamily.O

theorem max_raw_reduction (Z Rred r : ℝ) (hZ : 1<Z) (hR : 0<Rred) :
    max 1 (Z^r/Rred)=Z^(max (r-Real.logb Z Rred) 0) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have he : Z^r/Rred=Z^(r-Real.logb Z Rred) := by
    rw [Real.rpow_sub hz,Real.rpow_logb hz hZ.ne' hR]
  rw [he]
  by_cases h : 0≤ r-Real.logb Z Rred
  · rw [max_eq_left h,max_eq_right (Real.one_le_rpow hZ.le h)]
  · rw [max_eq_right (le_of_not_ge h),Real.rpow_zero,
      max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hZ.le (le_of_not_ge h))]

end SevenEighths.CenteredMomentExceptionalCappedAmplitude

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.EligibleEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEligibleEnergy
open HeckeFamily CenteredMomentActiveDivisorShell CenteredMomentActiveAllocation
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentDivisorRowEnergy
local notation "O" => ActualEisensteinCubic.O

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma Data.reduction_pos (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : 0<formalReductionFactor D a s.P :=
  mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))

end SevenEighths.CenteredMomentEligibleEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AllocatedCenteredCapped
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentAllocatedCenteredCapped
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle CenteredMomentExceptionalCappedAmplitude
open CenteredMomentCanonicalFirst
open CenteredMomentForcing CenteredMomentChildRows
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma plain_norm_le_reduction (L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2)))
    (P:ι→ℝ) (hP:∀i,1≤P i) (j:Fin 2):
    (Ideal.absNorm (selectedPlain L a j):ℝ)≤formalReductionFactor L a P:=by
  have hN (k:Fin 2):(1:ℝ)≤Ideal.absNorm (selectedPlain L a k):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero L Finset.univ a (Sum.inr k)))
  have hh:(Ideal.absNorm (selectedPlain L a j):ℝ)≤ selectedNorm L a:=by
    fin_cases j
    · exact le_mul_of_one_le_right (by positivity) (hN 1)
    · exact le_mul_of_one_le_left (by positivity) (hN 0)
  exact hh.trans (le_mul_of_one_le_right (selectedNorm_pos L a).le
    (Finset.one_le_prod (fun i _=>hP i)))

lemma allocated_lower (L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2)))
    (P:ι→ℝ) (hP:∀i,1≤P i) (Z r X:ℝ) (hZ:0<Z) (hX:Z^r≤X) (j:Fin 2):
    Z^r/formalReductionFactor L a P≤X/(Ideal.absNorm (selectedPlain L a j):ℝ):=by
  have hn:(0:ℝ)<Ideal.absNorm (selectedPlain L a j):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero L Finset.univ a (Sum.inr j)))
  exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hZ.le _) hn
    (plain_norm_le_reduction L a P hP j)).trans (div_le_div_of_nonneg_right hX hn.le)

lemma remaining_volume (L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2)))
    (P:ι→ℝ) (hP:∀i,0<P i) (T:ℝ):
    (T/selectedNorm L a)*(∏i:liveIndices L a,P i)=
      (T*∏i,P i)/formalReductionFactor L a P:=by
  rw [Finset.prod_coe_sort]
  apply (eq_div_iff (mul_pos (selectedNorm_pos L a) (Finset.prod_pos (fun i _=>hP i))).ne').mpr
  exact raw_scale_identity L a T P

end SevenEighths.CenteredMomentAllocatedCenteredCapped

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceDetectorCapped
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeRowClosure ConcretePrimeRowBridge CenteredMomentDetectorDictionary
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight CenteredExceptionalProfile
open CenteredMomentExceptionalCappedAmplitude
local notation "O" => HeckeFamily.O

theorem detector_capped_slots_uniform (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],∀Z : ℝ,1≤Z →
      ∀η : Character,∀m A z : O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^B → FixedInducingRow η Q m A z →
      ∀S : ι→Finset (Ideal O),∀β : ι→Ideal O→ℂ,∀p b M : ι→ℝ,
      (∀i,0<p i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀P∈S i,‖β i P‖≤M i) → (∀i,∀P∈S i,β i P≠0 → (P.absNorm:ℝ)≤b i*p i) →
      ∀r₁ r₂ : Bool,∀j k : ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z (detectorSchwartz r₁ j σ₁ t₁) (detectorSchwartz r₂ k σ₂ t₂)
        S β p h X₁ X₂ Y₁ Y₂ T‖≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(∏i,128*b i*M i)*(Real.sqrt (T*∏i,p i)/max 1 L) := by
  obtain ⟨J,hJ⟩:=detector_capped_rectangle_uniform ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro ι inst Z hZ η m A z hm hA hz hml hm2 hcond hex S β p b M hp hb hM hβ hN
    r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂ t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0<T:=hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) h‖≤(128*b i*M i)*p i := by
    convert (preTransparency := .instances) rowSlot_bound η m A z (S i) (β i) h (b i*p i) (M i)
      (mul_nonneg (hb i) (hp i).le) (hM i) (hβ i) (hN i) using 1 ; ring
  exact whole_product_normalization _ (fun i=>rowSlot η m A z (S i) (β i) h)
    (fun i=>128*b i*M i) p (C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J) T (max 1 L)
    (by positivity) hT (zero_lt_one.trans_le (le_max_left _ _))
    (fun i=>mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hp hslots
    (hbound Z hZ η m A z hm hA hz hml hm2 hcond hex r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
      t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AllocatedDetectorCapped
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAllocatedDetectorCapped
open HeckeFamily CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorRectangle CenteredMomentAllocatedCenteredCapped
open ConcretePrimeRowBridge CenteredMomentExceptionalCappedAmplitude
local notation "O" => HeckeFamily.O

theorem actual_detector_allocated_capped (ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀Z:ℝ,1<Z → ∀η:Character,∀m A z:O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀(S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b M:ι→ℝ),
      (∀i,1≤P i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀I∈S i,‖β i I‖≤M i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀(L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2))),
      ∀r₁ r₂:Bool,∀j k:ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T r:ℝ,Z^r≤X₁ → Z^r≤X₂ → Z^r≤Y₁ → Z^r≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖residualCenteredRow η m A z h S β P L a
        (detectorSchwartz r₁ j σ₁ t₁) (detectorSchwartz r₂ k σ₂ t₂) X₁ X₂ Y₁ Y₂ T‖≤
      C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(∏i:liveIndices L a,128*b i*M i)*
        (Real.sqrt ((T*∏i,P i)/formalReductionFactor L a P)/
          Z^(max (r-Real.logb Z (formalReductionFactor L a P)) 0)):=by
  obtain ⟨J,hJ⟩:=detector_capped_slots_uniform ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro ι _ _ Z hZ η m A z hm hA hz hmLam hm2 hcond hex S β P b M hP hb hM hβ hN
    L a r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂ t₁ t₂ h X₁ X₂ Y₁ Y₂ T r hX₁ hX₂ hY₁ hY₂ hXT hYT
  have hp (i:ι):0<P i:=zero_lt_one.trans_le (hP i)
  have hred:0<formalReductionFactor L a P:=mul_pos (selectedNorm_pos L a)
    (Finset.prod_pos (fun i _=>hp i))
  have hh:=hbound (ι:=liveIndices L a) Z hZ.le η m A z hm hA hz hmLam hm2 hcond hex
    (fun i=>S i) (fun i=>β i) (fun i=>P i) (fun i=>b i) (fun i=>M i)
    (fun i=>hp i) (fun i=>hb i) (fun i=>hM i) (fun i=>hβ i) (fun i=>hN i)
    r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂ t₁ t₂ h
    (X₁/Ideal.absNorm (selectedPlain L a 0)) (X₂/Ideal.absNorm (selectedPlain L a 1))
    (Y₁/Ideal.absNorm (selectedPlain L a 0)) (Y₂/Ideal.absNorm (selectedPlain L a 1))
    (T/selectedNorm L a) (Z^r/formalReductionFactor L a P)
    (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hred)
    (allocated_lower L a P hP Z r X₁ (zero_lt_one.trans hZ) hX₁ 0)
    (allocated_lower L a P hP Z r X₂ (zero_lt_one.trans hZ) hX₂ 1)
    (allocated_lower L a P hP Z r Y₁ (zero_lt_one.trans hZ) hY₁ 0)
    (allocated_lower L a P hP Z r Y₂ (zero_lt_one.trans hZ) hY₂ 1)
    (by rw [div_mul_div_comm,hXT];rfl) (by rw [div_mul_div_comm,hYT];rfl)
  rw [remaining_volume L a P hp T,max_raw_reduction Z _ r hZ hred] at hh
  exact hh

end SevenEighths.CenteredMomentAllocatedDetectorCapped

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AllocatedDetectorAmplitude
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAllocatedDetectorAmplitude
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRawEnergy CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction
open CenteredMomentAllocatedDetectorCapped CenteredMomentDetectorDictionary
open ConcretePrimeRowBridge CenteredMomentDivisorRows
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma slotControl_nonneg (s:Data ι):0≤ slotControl s:=by
  unfold slotControl
  exact mul_nonneg (Finset.prod_nonneg (fun i _=>(zero_le_one.trans (s.M_ge_one i))))
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (le_max_left _ _)))

lemma slot_product_bound (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))):
    (∏i∈frozenIndices D a,s.M i)*(∏i:liveIndices D a,128*max 0 (s.hi i)*s.M i)≤ slotControl s:=by
  have hf:(∏i∈frozenIndices D a,s.M i)≤∏i,s.M i:=
    Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
  have hl:(∏i:liveIndices D a,128*max 0 (s.hi i)*s.M i)≤∏i,max 1 (128*max 0 (s.hi i)*s.M i):=by
    have he := Finset.prod_coe_sort (liveIndices D a) (fun i:ι=>128*max 0 (s.hi i)*s.M i)
    rw [he]
    apply (Finset.prod_le_prod (fun i _=>mul_nonneg (mul_nonneg (by norm_num) (le_max_left _ _))
      (zero_le_one.trans (s.M_ge_one i))) (fun i _=>le_max_right 1 _)).trans
    exact Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (le_max_left _ _)) (fun i _ _=>le_max_left _ _)
  exact mul_le_mul hf hl (Finset.prod_nonneg (fun i _=>mul_nonneg (mul_nonneg (by norm_num) (le_max_left _ _)) (zero_le_one.trans (s.M_ge_one i))))
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i)))

omit [DecidableEq ι] in
lemma coefficient_support (s:Data ι) (i:ι) (I:Ideal O) (hI:s.coefficient i I≠0):
    (Ideal.absNorm I:ℝ)≤ max 0 (s.hi i)*s.P i:=by
  have hw:s.W i ((Ideal.absNorm I:ℝ)/s.P i)≠0:=right_ne_zero_of_mul hI
  exact (div_le_iff₀ (s.P_pos i)).mp ((s.support i hw).2.trans (le_max_right _ _))

theorem actual_allocated_amplitude (ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀(s:Data ι)(Z:ℝ),1<Z → (∀i,1≤ s.P i) →
      ∀z:O,s.m≠0 → s.A≠0 → z≠0 → goodLambda∣s.m → (2:O)∣s.m →
      (HeckeRowClosure.rowConductorBound s.η s.m 1 (s.A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow s.η Q s.m s.A z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))),
      ∀r₁ r₂:Bool,∀j k:ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ r:ℝ,s.W₁=detectorSchwartz r₁ j σ₁ t₁ → s.W₂=detectorSchwartz r₂ k σ₂ t₂ →
      Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ‖amplitude s D a z‖^2≤
        (C*Z^ε*(1+‖t₁‖+‖t₂‖+‖s.t‖)^J*slotControl s)^2*
          (s.X₁*s.X₂*∏i,s.P i)/
          ((formalReductionFactor D a s.P)^2*(Z^(max (r-Real.logb Z (formalReductionFactor D a s.P)) 0))^2):=by
  obtain ⟨J,hJ⟩:=actual_detector_allocated_capped ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hcap⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro ι _ _ s Z hZ hP z hm hA hz hml hm2 hcond hex D a r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
    t₁ t₂ r hW₁ hW₂ hX₁ hX₂ hY₁ hY₂
  have hb:=hcap ι Z hZ s.η s.m s.A z hm hA hz hml hm2 hcond hex s.slots s.coefficient s.P
    (fun i=>max 0 (s.hi i)) s.M hP (fun i=>le_max_left _ _) (fun i=>zero_le_one.trans (s.M_ge_one i))
    s.coefficient_bound (fun i I _ hi=>coefficient_support s i I hi) D a
    r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂ t₁ t₂ s.t s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) r
    hX₁ hX₂ hY₁ hY₂ rfl s.same_product
  rw [←hW₁,←hW₂] at hb
  have ha:=allocated_raw_energy s.η s.m s.A z s.t s.slots s.prime s.coefficient s.M s.P
    (fun i=>zero_le_one.trans (s.M_ge_one i)) s.P_pos s.coefficient_bound D a s.W₁ s.W₂
    s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.support₁ s.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos (mul_pos s.X₁_pos s.X₂_pos)
  have hred:=s.reduction_pos D a
  have hraw:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  let V:=s.X₁*s.X₂*∏i,s.P i
  let d:=formalReductionFactor D a s.P
  let H:=C*Z^ε*(1+‖t₁‖+‖t₂‖+‖s.t‖)^J
  let F:=∏i∈frozenIndices D a,s.M i
  let L:=∏i:liveIndices D a,128*max 0 (s.hi i)*s.M i
  let M:=Z^(max (r-Real.logb Z d) 0)
  have hH:0≤H:=by dsimp [H]; positivity
  have hM:0<M:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hFL:0≤F*L:=mul_nonneg
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i)))
    (Finset.prod_nonneg (fun i _=>mul_nonneg (mul_nonneg (by norm_num) (le_max_left _ _)) (zero_le_one.trans (s.M_ge_one i))))
  have hp:F*L≤ slotControl s:=slot_product_bound s D a
  calc
    ‖amplitude s D a z‖^2≤F^2/d*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
        s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2:=ha
    _≤F^2/d*(H*L*(Real.sqrt (V/d)/M))^2:=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (div_nonneg (sq_nonneg _) hred.le)
    _=(H*(F*L))^2*V/(d^2*M^2):=by
      rw [mul_pow,mul_pow,div_pow,Real.sq_sqrt (div_nonneg hraw.le hred.le)]
      dsimp only [V,d]
      field_simp [hred.ne']
    _≤(H*slotControl s)^2*V/(d^2*M^2):=by
      apply div_le_div_of_nonneg_right _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      apply mul_le_mul_of_nonneg_right _ hraw.le
      exact pow_le_pow_left₀ (mul_nonneg hH hFL) (mul_le_mul_of_nonneg_left hp hH) 2
    _=_:=rfl

end SevenEighths.CenteredMomentAllocatedDetectorAmplitude

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentDetectorDictionary
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u

lemma volume_pos {ι:Type u} [Fintype ι] (s:Data ι):0<volume s:=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

lemma norm_le_of_squared (x:ℂ) (H V d M:ℝ) (hH:0≤H) (hV:0≤V) (hd:0<d) (hM:0<M)
    (hb:‖x‖^2≤H^2*V/(d^2*M^2)):
    ‖x‖≤H*Real.sqrt V/(d*M):=by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  convert (preTransparency := .instances) hb using 1
  rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt hV]

lemma reduction_cap_identity {ι κ:Type u} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (s:Data ι) (v:Data κ) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))) (Z r:ℝ) (hZ:1<Z):
    1/(formalReductionFactor D a s.P*formalReductionFactor D b v.P*
      Z^(max (r-Real.logb Z (formalReductionFactor D a s.P)) 0))=
      exceptionalWeight s.toSource v.toSource D a b Z r:=by
  have hz:=zero_lt_one.trans hZ
  unfold exceptionalWeight
  rw [show -Real.logb Z (formalReductionFactor D a s.P)-Real.logb Z (formalReductionFactor D b v.P)-
      max (r-Real.logb Z (formalReductionFactor D a s.P)) 0=
      -(Real.logb Z (formalReductionFactor D a s.P)+Real.logb Z (formalReductionFactor D b v.P)+
        max (r-Real.logb Z (formalReductionFactor D a s.P)) 0) by ring,
    Real.rpow_neg hz.le,Real.rpow_add hz,Real.rpow_add hz,
    Real.rpow_logb hz hZ.ne' (s.reduction_pos D a),Real.rpow_logb hz hZ.ne' (v.reduction_pos D b)]
  exact one_div _

end SevenEighths.CenteredMomentExceptionalAmplitudePair

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ExceptionalAsymmetricSource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentExceptionalAsymmetricSource
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentDetectorDictionary
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell
open CenteredMomentExceptionalMaskedSource UniqueFactorizationMonoid CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

theorem actual_paired_asymmetric (ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(ι κ:Type u) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ],
      ∀(s:Data ι)(v:Data κ)(p q:Tests)(Z r rRight:ℝ),1<Z → ∀z:O,
      Admissible s p Q Z B r z → Admissible v q Q Z B rRight z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*Z^(2*ε)*p.heightWeight s.t^J*q.heightWeight v.t^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z r:=by
  obtain ⟨J,hJ⟩:=actual_allocated_amplitude ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C ^2,sq_pos_of_pos hC,?_⟩
  intro ι κ _ _ _ _ s v p q Z r rRight hZ z hs hv D a b
  have hpoint (α:Type u) [Fintype α] [DecidableEq α] (s:Data α)(p:Tests)(r0:ℝ)
      (hs:Admissible s p Q Z B r0 z)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2))):
      ‖amplitude s D a z‖≤C*Z^ε*p.heightWeight s.t^J*slotControl s*Real.sqrt (volume s)/
        (formalReductionFactor D a s.P*Z^(max (r0-Real.logb Z (formalReductionFactor D a s.P)) 0)):=by
    obtain ⟨hP,hm,hA,hz,hml,hm2,hcond,hex,hW₁,hW₂,hX₁,hX₂,hY₁,hY₂⟩:=hs
    apply norm_le_of_squared _ _ _ _ _
    · exact mul_nonneg (by dsimp [Tests.heightWeight]; positivity) (slotControl_nonneg s)
    · exact (volume_pos s).le
    · exact s.reduction_pos D a
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact hbound α s Z hZ hP z hm hA hz hml hm2 hcond hex D a
        (p.reverse 0) (p.reverse 1) (p.index 0) (p.index 1) (p.index_le 0) (p.index_le 1)
        (p.sigma 0) (p.sigma_mem 0) (p.sigma 1) (p.sigma_mem 1)
        (p.height 0) (p.height 1) r0 hW₁ hW₂ hX₁ hX₂ hY₁ hY₂
  have hl:=hpoint ι s p r hs a
  have hr:=hpoint κ v q rRight hv b
  have hcap:1≤Z^(max (rRight-Real.logb Z (formalReductionFactor D b v.P)) 0):=
    Real.one_le_rpow hZ.le (le_max_right _ _)
  have hr':‖amplitude v D b z‖≤
      C*Z^ε*q.heightWeight v.t^J*slotControl v*Real.sqrt (volume v)/formalReductionFactor D b v.P:=by
    apply hr.trans
    apply div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg (by dsimp [Tests.heightWeight]; positivity) (slotControl_nonneg v)) (Real.sqrt_nonneg _))
      (v.reduction_pos D b)
    exact le_mul_of_one_le_right (v.reduction_pos D b).le hcap
  apply (mul_le_mul hl hr' (norm_nonneg _) (by
    exact div_nonneg (mul_nonneg (mul_nonneg (by dsimp [Tests.heightWeight]; positivity)
      (slotControl_nonneg s)) (Real.sqrt_nonneg _)) (mul_nonneg (s.reduction_pos D a).le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))).trans_eq
  rw [←reduction_cap_identity s v D a b Z r hZ]
  have hp:Z^(2*ε)=(Z^ε)^2:=by rw [mul_comm (2:ℝ) ε,Real.rpow_mul (zero_lt_one.trans hZ).le,Real.rpow_two]
  rw [hp]
  ring

lemma reduction_ge_one {α:Type u} [Fintype α] [DecidableEq α]
    (s:Data α)(hP:∀i,1≤ s.P i)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2))):1≤formalReductionFactor D a s.P:=by
  have hn (j:Fin 2):(1:ℝ)≤Ideal.absNorm (selectedPlain D a j):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (hn 0) (hn 1))
    (Finset.one_le_prod (fun i _=>hP i))

lemma raw_cap_weight {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(hP:∀i,1≤ s.P i)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2)))(Z r:ℝ)(hZ:1<Z):
    exceptionalWeight s.toSource v.toSource D a b Z r=
      exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
  have hd:0≤Real.logb Z (formalReductionFactor D a s.P):=
    Real.logb_nonneg hZ (reduction_ge_one s hP D a)
  unfold exceptionalWeight
  congr 2
  by_cases hr:0≤ r
  · rw [max_eq_left hr]
  · have h0:r≤0:=le_of_not_ge hr
    rw [max_eq_right h0,max_eq_right (by linarith:r-Real.logb Z (formalReductionFactor D a s.P)≤0),
      max_eq_right (by linarith:0-Real.logb Z (formalReductionFactor D a s.P)≤0)]

end SevenEighths.CenteredMomentExceptionalAsymmetricSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalNormalize
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeTwist

theorem sourceControl_nonneg (S) (W : 𝓢(ℝ,ℂ)) : 0≤ sourceControl S W := apply_nonneg _ _

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalSlots
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
theorem capped_slots_source_control
    (a b ε B : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ, ∃ R : Finset (ℕ×ℕ), (0,0)∈R ∧
      ∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧
      ∀W₁ W₂ : 𝓢(ℝ,ℂ), Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀(ι : Type*) [Fintype ι],∀Z : ℝ,1≤Z →
      ∀(η : Character)(m A z : O),m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀(S : ι→Finset (Ideal O))(β : ι→Ideal O→ℂ)(P b M : ι→ℝ),
      (∀i,0<P i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀I∈S i,‖β i I‖≤M i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀t X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖≤
        C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖t‖)^J*(∏i,128*b i*M i)*(Real.sqrt (T*∏i,P i)/max 1 L) := by
  obtain ⟨J,R,hR,hJ⟩ := capped_rectangle_source_control a b ε B ha hb hε hB
  refine ⟨J,R,hR,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩ := hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ ι _ Z hZ η m A z hm hA hz hml hm2 hc he S β P b M hP hb hM hβ hN
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hR₁ := sourceControl_nonneg R W₁
  have hR₂ := sourceControl_nonneg R W₂
  have hT : 0<T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) t‖≤(128*b i*M i)*P i := by
    convert (preTransparency := .instances) rowSlot_bound η m A z (S i) (β i) t (b i*P i) (M i)
      (mul_nonneg (hb i) (hP i).le) (hM i) (hβ i) (hN i) using 1; ring
  exact whole_product_normalization _ (fun i=>rowSlot η m A z (S i) (β i) t)
    (fun i=>128*b i*M i) P (C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖t‖)^J) T (max 1 L) (by positivity) hT
    (zero_lt_one.trans_le (le_max_left _ _))
    (fun i=>mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hP hslots
    (hbound W₁ W₂ hs₁ hs₂ Z hZ η m A z hm hA hz hml hm2 hc he t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalAllocated
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorRectangle CenteredMomentAllocatedCenteredCapped
open ConcretePrimeRowBridge CenteredMomentExceptionalCappedAmplitude
local notation "O" => HeckeFamily.O
theorem allocated_source_control (lo hi ε B:ℝ) (hlo:0<lo) (hhi:0≤hi) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∃R:Finset (ℕ×ℕ),(0,0)∈R ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀W₁ W₂:𝓢(ℝ,ℂ), Function.support (W₁:ℝ→ℂ)⊆Set.Icc lo hi →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc lo hi →
      ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀Z:ℝ,1<Z → ∀η:Character,∀m A z:O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀(S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b M:ι→ℝ),
      (∀i,1≤P i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀I∈S i,‖β i I‖≤M i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀(L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2))),
      ∀h X₁ X₂ Y₁ Y₂ T r:ℝ,Z^r≤X₁ → Z^r≤X₂ → Z^r≤Y₁ → Z^r≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖residualCenteredRow η m A z h S β P L a
        W₁ W₂ X₁ X₂ Y₁ Y₂ T‖≤
      C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖h‖)^J*(∏i:liveIndices L a,128*b i*M i)*
        (Real.sqrt ((T*∏i,P i)/formalReductionFactor L a P)/
          Z^(max (r-Real.logb Z (formalReductionFactor L a P)) 0)):=by
  obtain ⟨J,R,hR,hJ⟩:=capped_slots_source_control lo hi ε B hlo hhi hε hB
  refine ⟨J,R,hR,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ ι _ _ Z hZ η m A z hm hA hz hmLam hm2 hcond hex S β P b M hP hb hM hβ hN
    L a h X₁ X₂ Y₁ Y₂ T r hX₁ hX₂ hY₁ hY₂ hXT hYT
  have hp (i:ι):0<P i:=zero_lt_one.trans_le (hP i)
  have hred:0<formalReductionFactor L a P:=mul_pos (selectedNorm_pos L a)
    (Finset.prod_pos (fun i _=>hp i))
  have hh:=hbound W₁ W₂ hs₁ hs₂ (liveIndices L a) Z hZ.le η m A z hm hA hz hmLam hm2 hcond hex
    (fun i=>S i) (fun i=>β i) (fun i=>P i) (fun i=>b i) (fun i=>M i)
    (fun i=>hp i) (fun i=>hb i) (fun i=>hM i) (fun i=>hβ i) (fun i=>hN i)
    h
    (X₁/Ideal.absNorm (selectedPlain L a 0)) (X₂/Ideal.absNorm (selectedPlain L a 1))
    (Y₁/Ideal.absNorm (selectedPlain L a 0)) (Y₂/Ideal.absNorm (selectedPlain L a 1))
    (T/selectedNorm L a) (Z^r/formalReductionFactor L a P)
    (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hred)
    (allocated_lower L a P hP Z r X₁ (zero_lt_one.trans hZ) hX₁ 0)
    (allocated_lower L a P hP Z r X₂ (zero_lt_one.trans hZ) hX₂ 1)
    (allocated_lower L a P hP Z r Y₁ (zero_lt_one.trans hZ) hY₁ 0)
    (allocated_lower L a P hP Z r Y₂ (zero_lt_one.trans hZ) hY₂ 1)
    (by rw [div_mul_div_comm,hXT];rfl) (by rw [div_mul_div_comm,hYT];rfl)
  rw [remaining_volume L a P hp T,max_raw_reduction Z _ r hZ hred] at hh
  exact hh

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalAmplitude
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRawEnergy CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction
open CenteredMomentAllocatedDetectorAmplitude ConcretePrimeRowBridge CenteredMomentDivisorRows
local notation "O" => HeckeFamily.O
theorem allocated_amplitude_source_control (lo hi ε B:ℝ) (hlo:0<lo) (hhi:0≤hi) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∃R:Finset (ℕ×ℕ),(0,0)∈R ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀W₁ W₂:𝓢(ℝ,ℂ), Function.support (W₁:ℝ→ℂ)⊆Set.Icc lo hi →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc lo hi →
      ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀(s:Data ι)(Z:ℝ),1<Z → (∀i,1≤ s.P i) →
      ∀z:O,s.m≠0 → s.A≠0 → z≠0 → goodLambda∣s.m → (2:O)∣s.m →
      (HeckeRowClosure.rowConductorBound s.η s.m 1 (s.A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow s.η Q s.m s.A z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))),
      ∀r:ℝ,s.W₁=W₁ → s.W₂=W₂ →
      Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ‖amplitude s D a z‖^2≤
        (C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖s.t‖)^J*slotControl s)^2*
          (s.X₁*s.X₂*∏i,s.P i)/
          ((formalReductionFactor D a s.P)^2*(Z^(max (r-Real.logb Z (formalReductionFactor D a s.P)) 0))^2):=by
  obtain ⟨J,R,hR,hJ⟩:=allocated_source_control lo hi ε B hlo hhi hε hB
  refine ⟨J,R,hR,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hcap⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ ι _ _ s Z hZ hP z hm hA hz hml hm2 hcond hex D a r hW₁ hW₂ hX₁ hX₂ hY₁ hY₂
  have hb:=hcap W₁ W₂ hs₁ hs₂ ι Z hZ s.η s.m s.A z hm hA hz hml hm2 hcond hex s.slots s.coefficient s.P
    (fun i=>max 0 (s.hi i)) s.M hP (fun i=>le_max_left _ _) (fun i=>zero_le_one.trans (s.M_ge_one i))
    s.coefficient_bound (fun i I _ hi=>coefficient_support s i I hi) D a
    s.t s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) r
    hX₁ hX₂ hY₁ hY₂ rfl s.same_product
  rw [←hW₁,←hW₂] at hb
  have ha:=allocated_raw_energy s.η s.m s.A z s.t s.slots s.prime s.coefficient s.M s.P
    (fun i=>zero_le_one.trans (s.M_ge_one i)) s.P_pos s.coefficient_bound D a s.W₁ s.W₂
    s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.support₁ s.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos (mul_pos s.X₁_pos s.X₂_pos)
  have hred:=s.reduction_pos D a
  have hraw:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  let V:=s.X₁*s.X₂*∏i,s.P i
  let d:=formalReductionFactor D a s.P
  let H:=C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖s.t‖)^J
  let F:=∏i∈frozenIndices D a,s.M i
  let L:=∏i:liveIndices D a,128*max 0 (s.hi i)*s.M i
  let M:=Z^(max (r-Real.logb Z d) 0)
  have hR₁:=sourceControl_nonneg R W₁
  have hR₂:=sourceControl_nonneg R W₂
  have hH:0≤H:=by dsimp [H]; positivity
  have hM:0<M:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hFL:0≤F*L:=mul_nonneg
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i)))
    (Finset.prod_nonneg (fun i _=>mul_nonneg (mul_nonneg (by norm_num) (le_max_left _ _)) (zero_le_one.trans (s.M_ge_one i))))
  have hp:F*L≤ slotControl s:=slot_product_bound s D a
  calc
    ‖amplitude s D a z‖^2≤F^2/d*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
        s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2:=ha
    _≤F^2/d*(H*L*(Real.sqrt (V/d)/M))^2:=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (div_nonneg (sq_nonneg _) hred.le)
    _=(H*(F*L))^2*V/(d^2*M^2):=by
      rw [mul_pow,mul_pow,div_pow,Real.sq_sqrt (div_nonneg hraw.le hred.le)]
      dsimp only [V,d]
      field_simp [hred.ne']
    _≤(H*slotControl s)^2*V/(d^2*M^2):=by
      apply div_le_div_of_nonneg_right _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      apply mul_le_mul_of_nonneg_right _ hraw.le
      exact pow_le_pow_left₀ (mul_nonneg hH hFL) (mul_le_mul_of_nonneg_left hp hH) 2
    _=_:=rfl

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u

lemma Profiles.control_nonneg {lo hi:ℝ} (p:Profiles lo hi) (R:Finset (ℕ×ℕ)) : 0≤p.control R :=
  mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

variable {lo hi:ℝ}

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonAsymmetric
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell
open CenteredMomentExceptionalMaskedSource UniqueFactorizationMonoid CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle CenteredMomentExceptionalAsymmetricSource
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

theorem actual_paired_asymmetric (lo hi ε B:ℝ) (hlo:0<lo) (hhi:0≤hi) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∃R:Finset (ℕ×ℕ),(0,0)∈R ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(ι κ:Type u) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ],
      ∀(s:Data ι)(v:Data κ)(p q:Profiles lo hi)(Z r rRight:ℝ),1<Z → ∀z:O,
      ProfileAdmissible s p Q Z B r z → ProfileAdmissible v q Q Z B rRight z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*p.control R*q.control R*Z^(2*ε)*(1+‖s.t‖)^J*(1+‖v.t‖)^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z r:=by
  obtain ⟨J,R,hR,hJ⟩:=allocated_amplitude_source_control lo hi ε B hlo hhi hε hB
  refine ⟨J,R,hR,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C ^2,sq_pos_of_pos hC,?_⟩
  intro ι κ _ _ _ _ s v p q Z r rRight hZ z hs hv D a b
  have hpoint (α:Type u) [Fintype α] [DecidableEq α] (s:Data α)(p:Profiles lo hi)(r0:ℝ)
      (hs:ProfileAdmissible s p Q Z B r0 z)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2))):
      ‖amplitude s D a z‖≤C*p.control R*Z^ε*(1+‖s.t‖)^J*slotControl s*Real.sqrt (volume s)/
        (formalReductionFactor D a s.P*Z^(max (r0-Real.logb Z (formalReductionFactor D a s.P)) 0)):=by
    have hpc := Profiles.control_nonneg p R
    obtain ⟨hP,hm,hA,hz,hml,hm2,hcond,hex,hW₁,hW₂,hX₁,hX₂,hY₁,hY₂⟩:=hs
    apply norm_le_of_squared _ _ _ _ _
    · exact mul_nonneg (by positivity) (slotControl_nonneg s)
    · exact (volume_pos s).le
    · exact s.reduction_pos D a
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact hbound (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
        α s Z hZ hP z hm hA hz hml hm2 hcond hex D a r0 hW₁ hW₂ hX₁ hX₂ hY₁ hY₂

  have hpc := Profiles.control_nonneg p R
  have hqc := Profiles.control_nonneg q R
  have hl:=hpoint ι s p r hs a
  have hr:=hpoint κ v q rRight hv b
  have hcap:1≤Z^(max (rRight-Real.logb Z (formalReductionFactor D b v.P)) 0):=
    Real.one_le_rpow hZ.le (le_max_right _ _)
  have hr':‖amplitude v D b z‖≤
      C*q.control R*Z^ε*(1+‖v.t‖)^J*slotControl v*Real.sqrt (volume v)/formalReductionFactor D b v.P:=by
    apply hr.trans
    apply div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg (by positivity) (slotControl_nonneg v)) (Real.sqrt_nonneg _))
      (v.reduction_pos D b)
    exact le_mul_of_one_le_right (v.reduction_pos D b).le hcap
  apply (mul_le_mul hl hr' (norm_nonneg _) (by
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (slotControl_nonneg s)) (Real.sqrt_nonneg _)) (mul_nonneg (s.reduction_pos D a).le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))).trans_eq
  rw [←reduction_cap_identity s v D a b Z r hZ]
  have hp:Z^(2*ε)=(Z^ε)^2:=by rw [mul_comm (2:ℝ) ε,Real.rpow_mul (zero_lt_one.trans hZ).le,Real.rpow_two]
  rw [hp]
  ring

theorem actual_paired_capped_oai (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(α κ:Type u) [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ],
      ∀(s:Data α)(v:Data κ)(p q:Profiles wlo whi)(Z r rRight:ℝ),1<Z → ∀z:O,
      ProfileAdmissible s p Q Z B r z → ProfileAdmissible v q Q Z B rRight z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*p.control Sprofile*q.control Sprofile*Z^(2*ε)*(1+‖s.t‖)^J*(1+‖v.t‖)^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_paired_asymmetric wlo whi ε B hwlo hwhi hε hB
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro α κ _ _ _ _ s v p q Z r rRight hZ z hs hv D a b
  rw [←raw_cap_weight s v hs.1 D a b Z r hZ]
  exact hbound α κ s v p q Z r rRight hZ z hs hv D a b

end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
end

theorem solution.{u} : type_of% @OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalCommon.actual_paired_capped_oai.{u} := @OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalCommon.actual_paired_capped_oai.{u}
