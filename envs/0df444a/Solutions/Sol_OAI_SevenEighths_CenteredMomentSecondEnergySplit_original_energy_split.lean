-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentSecondEnergySplit.original_energy_split
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:58:53.270887+00:00
-- url     : https://prove2.me/submissions/d9dbf57a-4aa4-45c4-b2e2-f06eec262ccc

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondRetainedAggregate_original_retained_energy_GV

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Scale
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentScale
open CenteredMomentSmooth EisensteinSchwartzPoisson

theorem logarithmic_kernel_argument (K H A B K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hA : 0 < A) (hB : 0 < B)
    (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    (K₀ * H₀ / (A₀ * B₀)) *
      Real.exp (Real.log (K / K₀) + Real.log (H / H₀) -
        Real.log (A / A₀) - Real.log (B / B₀)) = K * H / (A * B) := by
  rw [Real.exp_sub, Real.exp_sub, Real.exp_add,
    Real.exp_log (div_pos hK hK₀), Real.exp_log (div_pos hH hH₀),
    Real.exp_log (div_pos hA hA₀), Real.exp_log (div_pos hB hB₀)]
  field_simp

theorem rootWindow_log_ratio (V : ℝ → ℂ) (A A₀ : ℝ) (hA : 0 < A) (hA₀ : 0 < A₀) :
    rootWindow V (Real.log (A / A₀)) =
      (Real.sqrt A₀ : ℂ) * V (Real.log (A / A₀)) / (Real.sqrt A : ℂ) := by
  rw [rootWindow, Real.exp_log (div_pos hA hA₀), Real.sqrt_div hA.le, Complex.ofReal_div]
  field_simp

theorem wholeKernel_actual (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (K H A B K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hA : 0 < A) (hB : 0 < B)
    (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    wholeKernel W V (K₀ * H₀ / (A₀ * B₀))
      (Real.log (K / K₀)) (Real.log (H / H₀))
      (Real.log (A / A₀)) (Real.log (B / B₀)) =
      (((Real.sqrt A₀ : ℂ) * (Real.sqrt B₀ : ℂ)) /
        ((Real.sqrt A : ℂ) * (Real.sqrt B : ℂ))) *
      (V 0 (Real.log (K / K₀)) * V 1 (Real.log (H / H₀)) *
        V 2 (Real.log (A / A₀)) * V 3 (Real.log (B / B₀))) *
      paperRadialFourier W (K * H / (A * B)) := by
  rw [wholeKernel, rootWindow_log_ratio _ A A₀ hA hA₀,
    rootWindow_log_ratio _ B B₀ hB hB₀,
    logarithmic_kernel_argument K H A B K₀ H₀ A₀ B₀ hK hH hA hB hK₀ hH₀ hA₀ hB₀]
  ring

end SevenEighths.CenteredMomentScale

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SectorLocalization
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSectorLocalization
open CubicEisenstein ConcreteTraceCRT EisensteinSchwartzPoisson CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

theorem dyadicScale_add (n : ℤ) : dyadicScale (n+1)=2*dyadicScale n := by
  simp only [dyadicScale,zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),zpow_one]
  ring

theorem dyadicWeight_outside_pair (q : ℝ) (k : ℤ)
    (hlo : dyadicScale k ≤ q) (hhi : q < dyadicScale (k+1))
    (n : ℤ) (hn : n ∉ ({k+1,k+2} : Finset ℤ)) : dyadicWeight n q=0 := by
  have hn₁ : n ≠ k+1 := by simpa using fun h => hn (by simp [h])
  have hn₂ : n ≠ k+2 := by simpa using fun h => hn (by simp [h])
  by_cases hnk : n ≤ k
  · exact dyadicWeight_zero_high n q ((zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hnk).trans hlo)
  · have hkn : k+3 ≤ n := by omega
    have hmono : dyadicScale (k+3) ≤ dyadicScale n :=
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hkn
    have he : dyadicScale (k+3)=4*dyadicScale (k+1) := by
      rw [show k+3=(k+1)+1+1 by omega,dyadicScale_add,dyadicScale_add]
      ring
    apply dyadicWeight_zero_low
    rw [he] at hmono
    linarith

theorem dyadicWeight_partition (q : ℝ) (hq : 0 < q) : ∑' n,dyadicWeight n q=1 := by
  obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow hq (by norm_num : (1:ℝ) < 2)
  rw [tsum_eq_sum (s := {k+1,k+2}) (dyadicWeight_outside_pair q k hlo hhi)]
  change dyadicScale k ≤ q at hlo
  change q < dyadicScale (k+1) at hhi
  have hk : k+1 ≠ k+2 := by omega
  rw [Finset.sum_pair hk]
  simp only [dyadicWeight,annulus]
  have h₁ : 2*(q/dyadicScale (k+1))=q/dyadicScale k := by
    rw [dyadicScale_add]; field_simp
  have h₂ : 2*(q/dyadicScale (k+2))=q/dyadicScale (k+1) := by
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]; field_simp
  rw [h₁,h₂,cutoff_zero _ ((le_div_iff₀ (dyadicScale_pos k)).mpr (by simpa using hlo))]
  have hs : q/dyadicScale (k+2) ≤ 1/2 := by
    apply (div_le_iff₀ (dyadicScale_pos (k+2))).mpr
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]
    linarith
  rw [cutoff_one _ hs]
  ring

theorem dyadicWeight_zero_nonpos (n : ℤ) (q : ℝ) (hq : q ≤ 0) : dyadicWeight n q=0 :=
  dyadicWeight_zero_low n q (hq.trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))

theorem retainedWeight_zero_nonpos (R q : ℝ) (hq : q ≤ 0) : retainedWeight R q=0 := by
  simp [retainedWeight,dyadicWeight_zero_nonpos _ q hq]

theorem retainedWeight_zero_above (R q : ℝ) (hq : 4*R ≤ q) : retainedWeight R q=0 := by
  unfold retainedWeight
  trans ∑' _n : ℤ, (0:ℝ)
  · apply tsum_congr
    intro n
    split_ifs with hn
    · exact dyadicWeight_zero_high n q ((retained_scale_le R n hn).trans hq)
    · rfl
  · exact tsum_zero

theorem retainedWeight_enclosure (R q : ℝ) (hq : retainedWeight R q ≠ 0) : 0 < q ∧ q ≤ 4*R := by
  constructor
  · exact lt_of_not_ge (fun h => hq (retainedWeight_zero_nonpos R q h))
  · exact le_of_not_gt (fun h => hq (retainedWeight_zero_above R q h.le))

theorem annulus_pos (x : ℝ) (hlo : 1/4 < x) (hhi : x < 1) : 0 < annulus x := by
  by_cases hx : x ≤ 1/2
  · rw [annulus,cutoff_one x hx]
    have h := Real.smoothTransition.lt_one_of_lt_one (by linarith : 2-2*(2*x) < 1)
    exact sub_pos.mpr h
  · rw [annulus,cutoff_zero (2*x) (by linarith),sub_zero]
    exact Real.smoothTransition.pos_of_pos (by linarith)

theorem dyadicWeight_support_eq (n : ℤ) :
    Function.support (dyadicWeight n)=Set.Ioo (dyadicScale n/4) (dyadicScale n) := by
  apply Set.Subset.antisymm (dyadicWeight_support n)
  intro q hq
  apply ne_of_gt
  apply annulus_pos
  · apply (lt_div_iff₀ (dyadicScale_pos n)).mpr
    linarith [hq.1]
  · exact (div_lt_one (dyadicScale_pos n)).mpr hq.2

theorem dyadicWeight_tsupport_eq (n : ℤ) :
    tsupport (dyadicWeight n)=Set.Icc (dyadicScale n/4) (dyadicScale n) := by
  rw [tsupport,dyadicWeight_support_eq,closure_Ioo]
  linarith [dyadicScale_pos n]

theorem normValue_mul (v h : O) : normValue (v*h)=normValue v*normValue h := by
  simp only [normValue,← Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]

theorem normValue_pos (h : O) (hh : h ≠ 0) : 0 < normValue h := by
  unfold normValue
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

theorem normValue_ge_one (h : O) (hh : h ≠ 0) : 1 ≤ normValue h := by
  unfold normValue
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

theorem retained_norm_enclosure (R : ℝ) (v h : O) (hv : v ≠ 0)
    (hne : retainedWeight R (normValue (v*h)) ≠ 0) : normValue h ≤ 4*R/normValue v := by
  have hb := (retainedWeight_enclosure R _ hne).2
  rw [normValue_mul] at hb
  apply (le_div_iff₀ (normValue_pos v hv)).mpr
  nlinarith

theorem retained_product_ne_zero (R : ℝ) (v h : O)
    (hne : retainedWeight R (normValue (v*h)) ≠ 0) : v ≠ 0 ∧ h ≠ 0 := by
  have hp := (retainedWeight_enclosure R _ hne).1
  constructor <;> intro hz <;> simp [hz,normValue] at hp

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondWholeKernel
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondWholeKernel
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson CompletedGauss
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentScale CenteredMomentSmooth
open CenteredMomentFirstWholeKernel CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

theorem secondEffectiveScale_pos (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (A : O) (hA : A≠0) (K : ℝ) (hK : 0<K) : 0<secondEffectiveScale C D A K := by
  apply div_pos (mul_pos hK (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hA))))
  exact mul_pos (CenteredMomentFirstScale.norm_pos C hC) (CenteredMomentFirstScale.norm_pos D hD)

theorem primary_norm_sq (I : Ideal O) (hI : Supported I) :
    ‖eisEmbedding (primaryGenerator I)‖^2=(Ideal.absNorm I:ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,primary_span_supported I hI]

theorem second_kernel_argument (C D a b : Ideal O)
    (hC : Supported C) (hD : Supported D) (ha : Supported a) (hb : Supported b)
    (A h : O) (K : ℝ) :
    K*‖eisEmbedding (A*h)‖^2/
      ‖eisEmbedding (primaryGenerator (C*a)*primaryGenerator (D*b))‖^2=
      secondEffectiveScale C D A K*‖eisEmbedding h‖^2/((Ideal.absNorm a:ℝ)*(Ideal.absNorm b:ℝ)) := by
  simp only [map_mul,norm_mul,mul_pow,primary_norm_sq (C*a) ((supported_mul_iff _ _).mpr ⟨hC,ha⟩),
    primary_norm_sq (D*b) ((supported_mul_iff _ _).mpr ⟨hD,hb⟩),map_mul,Nat.cast_mul,secondEffectiveScale]
  ring

theorem common_normalized_kernel (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (k H a b C D K K₀ H₀ A₀ B₀ : ℝ)
    (hk : 0<k) (hH : 0<H) (ha : 0<a) (hb : 0<b)
    (hC : 0<C) (hD : 0<D) (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    (K:ℂ)/((Real.sqrt (C*a):ℂ)*(Real.sqrt (D*b):ℂ))*
      windows V k H a b K₀ H₀ A₀ B₀*paperRadialFourier W (k*H/(a*b))=
      (K:ℂ)/((Real.sqrt C:ℂ)*(Real.sqrt D:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ))*
        wholeKernel W V (K₀*H₀/(A₀*B₀))
          (Real.log (k/K₀)) (Real.log (H/H₀)) (Real.log (a/A₀)) (Real.log (b/B₀)) := by
  rw [wholeKernel_actual W V k H a b K₀ H₀ A₀ B₀ hk hH ha hb hK₀ hH₀ hA₀ hB₀]
  rw [Real.sqrt_mul hC.le a,Real.sqrt_mul hD.le b]
  simp only [Complex.ofReal_mul,windows]
  have hc : (Real.sqrt C:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hC).ne'
  have hd : (Real.sqrt D:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hD).ne'
  have haa : (Real.sqrt A₀:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hA₀).ne'
  have hbb : (Real.sqrt B₀:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB₀).ne'
  field_simp

theorem second_frequency_whole_kernel (C D a b : Ideal O)
    (hC : Supported C) (hD : Supported D) (ha : Supported a) (hb : Supported b)
    (A h : O) (hA : A≠0) (hh : h≠0) (K : ℝ) (hK : 0<K)
    (F : ℂ) (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K₀ H₀ A₀ B₀ : ℝ)
    (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    let k := secondEffectiveScale C D A K
    ((K:ℂ)/((Real.sqrt (Ideal.absNorm (C*a):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (D*b):ℝ):ℂ)))*F*
      windows V k (‖eisEmbedding h‖^2) (Ideal.absNorm a:ℝ) (Ideal.absNorm b:ℝ) K₀ H₀ A₀ B₀*
      paperRadialFourier W (K*‖eisEmbedding (A*h)‖^2/
        ‖eisEmbedding (primaryGenerator (C*a)*primaryGenerator (D*b))‖^2)=
      ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
        (Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*F*
        wholeKernel W V (K₀*H₀/(A₀*B₀))
          (Real.log (k/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
          (Real.log ((Ideal.absNorm a:ℝ)/A₀)) (Real.log ((Ideal.absNorm b:ℝ)/B₀)) := by
  dsimp only
  rw [second_kernel_argument C D a b hC hD ha hb]
  simp only [map_mul,Nat.cast_mul]
  have he := common_normalized_kernel W V (secondEffectiveScale C D A K) (‖eisEmbedding h‖^2)
    (Ideal.absNorm a:ℝ) (Ideal.absNorm b:ℝ) (Ideal.absNorm C:ℝ) (Ideal.absNorm D:ℝ)
    K K₀ H₀ A₀ B₀ (secondEffectiveScale_pos C D hC.1 hD.1 A hA K hK)
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)))
    (CenteredMomentFirstScale.norm_pos a ha.1) (CenteredMomentFirstScale.norm_pos b hb.1)
    (CenteredMomentFirstScale.norm_pos C hC.1) (CenteredMomentFirstScale.norm_pos D hD.1)
    hK₀ hH₀ hA₀ hB₀
  convert (preTransparency := .instances) congrArg (fun z : ℂ => F*z) he using 1 <;> ring

end SevenEighths.CenteredMomentSecondWholeKernel

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ActiveSource
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentActiveSource
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentGaussEnergy
open CenteredMomentLiveDomain CenteredMomentOriginalChildEnergy CenteredMomentSecondLocalization
open CenteredMomentFirstSectors CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O

theorem supportedColumns_active (S : Finset (Ideal O)) (β : Ideal O → ℂ) :
    supportedColumns (activeSource S β)=(supportedColumns S).filter (fun I => β I≠0) := by
  ext I
  simp only [supportedColumns,activeSource,Finset.mem_filter]
  tauto

theorem secondRetainedEnergy_eq_sum (η : HeckeFamily.Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K T Z ξ : ℝ) :
    secondRetainedEnergy η t S β W K T Z ξ=
      ∑I∈supportedColumns S,∑J∈supportedColumns S,
        ((β I*CenteredMomentHeckeColumnWindow.heightCoeff η t I)*
          star (β J*CenteredMomentHeckeColumnWindow.heightCoeff η t J))*
          retainedKernel I J W K T Z ξ := by
  unfold secondRetainedEnergy
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro I hI
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [retainedKernel,dif_pos (Finset.mem_filter.mp I.property).2,
    dif_pos (Finset.mem_filter.mp J.property).2]

theorem secondRetainedEnergy_active (η : HeckeFamily.Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K T Z ξ : ℝ) :
    secondRetainedEnergy η t (activeSource S β) β W K T Z ξ=
      secondRetainedEnergy η t S β W K T Z ξ := by
  rw [secondRetainedEnergy_eq_sum,secondRetainedEnergy_eq_sum,supportedColumns_active]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hi : β I=0
  · simp [hi]
  · rw [if_pos hi]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hj : β J=0 <;> simp [hj]

theorem residualPool_data (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (H : ℝ) (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C : Ideal O) (hC : C≠0) (a : Ideal O)
    (ha : a∈residualPool C hC (supportedColumns (activeSource S β))) :
    C*a∈S ∧ β (C*a)≠0 ∧ Supported (C*a) ∧ a≠0 ∧
      1≤(Ideal.absNorm a:ℝ) ∧ (Ideal.absNorm a:ℝ)≤H/(Ideal.absNorm C:ℝ) := by
  have hm := (mem_residualPool C hC _ a).mp ha
  obtain ⟨hm,hsa⟩ := Finset.mem_filter.mp hm
  obtain ⟨hm,hβ⟩ := (mem_activeSource S β (C*a)).mp hm
  have ha0 : a≠0 := right_ne_zero_of_mul hsa.1
  have hpos := CenteredMomentFirstScale.norm_pos C hC
  have hab := hH (C*a) hm hβ
  rw [map_mul,Nat.cast_mul] at hab
  refine ⟨hm,hβ,hsa,ha0,?_,?_⟩
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ha0)
  · exact (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hab)

end SevenEighths.CenteredMomentActiveSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DyadicCount
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.CenteredMomentDyadicCount
open CenteredMomentSectorLocalization

lemma logb_dyadicScale (n : ℤ) : Real.logb 2 (dyadicScale n)=(n:ℝ) := by
  rw [dyadicScale,←Real.rpow_intCast,Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num)]

lemma mem_indices_iff_scale (a b : ℝ) (ha : 0<a) (hb : 0<b) (n : ℤ) :
    n∈indices a b ↔ a≤dyadicScale n ∧ dyadicScale n≤4*b := by
  rw [indices,Finset.mem_Icc,Int.ceil_le,Int.le_floor]
  rw [←logb_dyadicScale n]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨(Real.logb_le_logb (by norm_num) ha (dyadicScale_pos n)).mp h1,
      (Real.logb_le_logb (by norm_num) (dyadicScale_pos n) (by positivity)).mp h2⟩
  · rintro ⟨h1,h2⟩
    exact ⟨Real.logb_le_logb_of_le (by norm_num) ha h1,
      Real.logb_le_logb_of_le (by norm_num) (dyadicScale_pos n) h2⟩

lemma mem_indices_iff_whole_support (a b : ℝ) (ha : 0<a) (hab : a≤b) (n : ℤ) :
    n∈indices a b ↔ ∃q∈Icc a b,q∈tsupport (dyadicWeight n) := by
  rw [mem_indices_iff_scale a b ha (ha.trans_le hab) n]
  constructor
  · rintro ⟨hlo,hhi⟩
    refine ⟨max a (dyadicScale n/4),⟨le_max_left _ _,max_le hab (by linarith)⟩,?_⟩
    rw [dyadicWeight_tsupport_eq]
    exact ⟨le_max_right _ _,max_le hlo (by linarith [dyadicScale_pos n])⟩
  · rintro ⟨q,hq,hq'⟩
    have hh := dyadicWeight_tsupport n hq'
    exact ⟨hq.1.trans hh.2,by linarith [hq.2,hh.1]⟩

lemma support_indices (a b q : ℝ) (ha : 0<a) (hq : q∈Icc a b)
    (n : ℤ) (hne : dyadicWeight n q≠0) : n∈indices a b :=
  (mem_indices_iff_whole_support a b ha (hq.1.trans hq.2) n).mpr
    ⟨q,hq,subset_tsupport _ hne⟩

lemma dyadic_partition_on_interval (a b q : ℝ) (ha : 0<a) (hq : q∈Icc a b) :
    (∑n∈indices a b,dyadicWeight n q)=1 := by
  rw [←dyadicWeight_partition q (ha.trans_le hq.1)]
  symm
  apply tsum_eq_sum
  intro n hn
  by_contra hne
  exact hn (support_indices a b q ha hq n hne)

end SevenEighths.CenteredMomentDyadicCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.LogDyadic
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentLogDyadic
open CenteredMomentSectorLocalization CenteredMomentFirstWholeKernel

theorem logAnnulus_log (q H : ℝ) (hq : 0<q) (hH : 0<H) :
    logAnnulus (Real.log (q/H))=(annulus (q/H):ℂ) := by
  rw [logAnnulus,Real.exp_log (div_pos hq hH)]

theorem actual_dyadic_log_window (n : ℤ) (q : ℝ) (hq : 0<q) :
    (dyadicWeight n q:ℂ)=logAnnulus (Real.log (q/dyadicScale n)) := by
  rw [logAnnulus_log q _ hq (dyadicScale_pos n)];rfl

theorem actual_product_windows (k H a b : ℝ)
    (hk : 0<k) (hH : 0<H) (ha : 0<a) (hb : 0<b) (n : Fin 4→ℤ) :
    ((dyadicWeight (n 0) k*dyadicWeight (n 1) H*
      dyadicWeight (n 2) a*dyadicWeight (n 3) b:ℝ):ℂ)=
      windows (fun _=>logAnnulus) k H a b
        (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  simp only [Complex.ofReal_mul,actual_dyadic_log_window (n 0) k hk,
    actual_dyadic_log_window (n 1) H hH,actual_dyadic_log_window (n 2) a ha,
    actual_dyadic_log_window (n 3) b hb,windows]

end SevenEighths.CenteredMomentLogDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondCanonical
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonical
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentSupportedCorrelation
open CenteredMomentSourceRow UniqueFactorizationMonoid CenteredMomentSupport CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem commonPrime_supported_ideal (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Supported P.val :=
  supported_of_dvd P.val C hC
    (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1))

theorem commonPrime_span (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Ideal.span {commonPrime C D P}=P.val :=
  primary_span_supported P.val (commonPrime_supported_ideal C D hC P)

theorem commonPrime_supported (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Supported (Ideal.span {commonPrime C D P}) := by
  rw [commonPrime_span C D hC P]
  exact commonPrime_supported_ideal C D hC P

end SevenEighths.CenteredMomentSecondCanonical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalFrequency
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalFrequency
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondLedger
open CenteredMomentPartition CenteredMomentSupport CenteredMomentSupportedCorrelation
open CenteredMomentCorrelation CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem commonFrequencyGenerator_ne_zero (C D : Ideal O) (hC : Supported C) :
    commonFrequencyGenerator C D≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  exact pow_ne_zero _ (supported_element_ne_zero _ (commonPrime_supported C D hC P))

end SevenEighths.CenteredMomentSecondCanonicalFrequency

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalNonunit
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalNonunit
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentCanonicalFirst
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentProductCRT
open CenteredMomentSupport
local notation "O" => ActualEisensteinCubic.O

theorem nonunitFrequencyGenerator_ne_zero (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) : nonunitFrequencyGenerator C D U≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _=>
    CenteredMomentSupportedCorrelation.supported_element_ne_zero _ (commonPrime_supported C D hC P))

end SevenEighths.CenteredMomentSecondCanonicalNonunit

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalWindow
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondPhysicalWindow
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorFrequency CenteredMomentSecondSectorColumns
open CenteredMomentSecondWholeKernel CenteredMomentFirstWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSmooth CenteredMomentLogDyadic
local notation "O" => ActualEisensteinCubic.O

theorem physical_kernel_window (C D I J : Ideal O)
    (hC : Supported C) (hD : Supported D) (hI : Supported I) (hJ : Supported J)
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K)
    (V : Fin 4→ℝ→ℂ) (K₀ H₀ A₀ B₀ : ℝ)
    (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    physicalKernel C D W K R (A*h) I J*
      windows V (secondEffectiveScale C D A K) (normValue h)
        (Ideal.absNorm I:ℝ) (Ideal.absNorm J:ℝ) K₀ H₀ A₀ B₀=
      ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
        (Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*
        (retainedWeight R (normValue (A*h)):ℂ)*
          wholeKernel W V (K₀*H₀/(A₀*B₀))
            (Real.log (secondEffectiveScale C D A K/K₀)) (Real.log (normValue h/H₀))
            (Real.log ((Ideal.absNorm I:ℝ)/A₀)) (Real.log ((Ideal.absNorm J:ℝ)/B₀)) := by
  have he := second_frequency_whole_kernel C D I J hC hD hI hJ A h hA hh K hK 1 W V
    K₀ H₀ A₀ B₀ hK₀ hH₀ hA₀ hB₀
  dsimp only at he
  simp only [mul_one,normValue_eq_embedding] at he ⊢
  have hd : ‖eisEmbedding (CompletedGauss.primaryGenerator (C*I)*
      CompletedGauss.primaryGenerator (D*J))‖^2=
      (Ideal.absNorm (C*I):ℝ)*(Ideal.absNorm (D*J):ℝ) := by
    rw [map_mul,norm_mul,mul_pow,primary_norm_sq _ ((supported_mul_iff _ _).mpr ⟨hC,hI⟩),
      primary_norm_sq _ ((supported_mul_iff _ _).mpr ⟨hD,hJ⟩)]
  rw [hd] at he
  unfold physicalKernel
  rw [hd]
  simp only [normValue_eq_embedding]
  convert (preTransparency := .instances) congrArg (fun x : ℂ=>(retainedWeight R (‖eisEmbedding (A*h)‖^2):ℂ)*x) he using 1 <;> ring

theorem physical_kernel_dyadic (C D I J : Ideal O)
    (hC : Supported C) (hD : Supported D) (hI : Supported I) (hJ : Supported J)
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K)
    (n : Fin 4→ℤ) :
    physicalKernel C D W K R (A*h) I J*
      ((dyadicWeight (n 0) (secondEffectiveScale C D A K)*dyadicWeight (n 1) (normValue h)*
        dyadicWeight (n 2) (Ideal.absNorm I:ℝ)*dyadicWeight (n 3) (Ideal.absNorm J:ℝ):ℝ):ℂ)=
      ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
        (Real.sqrt (dyadicScale (n 2)):ℂ)*(Real.sqrt (dyadicScale (n 3)):ℂ)))*
        (retainedWeight R (normValue (A*h)):ℂ)*
          wholeKernel W (fun _=>logAnnulus)
            (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
            (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
            (Real.log (normValue h/dyadicScale (n 1)))
            (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
            (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3))) := by
  rw [actual_product_windows _ _ _ _ (secondEffectiveScale_pos C D hC.1 hD.1 A hA K hK)
    (normValue_pos h hh) (CenteredMomentFirstScale.norm_pos I hI.1)
    (CenteredMomentFirstScale.norm_pos J hJ.1)]
  exact physical_kernel_window C D I J hC hD hI hJ A h hA hh W K R hK _ _ _ _ _
    (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)

end SevenEighths.CenteredMomentSecondPhysicalWindow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondDyadicPartition
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondDyadicPartition
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSecondSectorRetained CenteredMomentSecondPhysicalWindow
open CenteredMomentSecondWholeKernel CenteredMomentFirstWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSmooth CenteredMomentLogDyadic CenteredMomentDyadicCount
local notation "O" => ActualEisensteinCubic.O

theorem dyadic_product_partition (a b q : Fin 4→ℝ)
    (ha : ∀i,0<a i) (hq : ∀i,q i∈Set.Icc (a i) (b i)) :
    (∑ n : Blocks a b,∏ i : Fin 4,dyadicWeight (n i) (q i))=1 := by
  change (∑ n : (∀ i : Fin 4,↥(indices (a i) (b i))),∏ i : Fin 4,dyadicWeight (n i) (q i))=1
  rw [←Fintype.prod_sum (fun (i : Fin 4) (n : indices (a i) (b i))=>dyadicWeight n (q i))]
  have he (i : Fin 4) : (∑ n : indices (a i) (b i),dyadicWeight n (q i))=1 := by
    rw [Finset.sum_coe_sort (indices (a i) (b i)) (fun n : ℤ=>dyadicWeight n (q i))]
    exact dyadic_partition_on_interval _ _ _ (ha i) (hq i)
  simp_rw [he]
  simp

theorem physical_kernel_dyadic_partition (C D I J : Ideal O)
    (hC : Supported C) (hD : Supported D) (hI : Supported I) (hJ : Supported J)
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K)
    (a b : Fin 4→ℝ) (ha : ∀i,0<a i)
    (hband : ∀i, (![secondEffectiveScale C D A K,normValue h,
      (Ideal.absNorm I:ℝ),(Ideal.absNorm J:ℝ)] : Fin 4→ℝ) i∈Set.Icc (a i) (b i)) :
    physicalKernel C D W K R (A*h) I J=
      ∑ n : Blocks a b,
        ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
          (Real.sqrt (dyadicScale (n 2)):ℂ)*(Real.sqrt (dyadicScale (n 3)):ℂ)))*
          (retainedWeight R (normValue (A*h)):ℂ)*
            wholeKernel W (fun _=>logAnnulus)
              (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
              (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
              (Real.log (normValue h/dyadicScale (n 1)))
              (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
              (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3))) := by
  let q : Fin 4→ℝ := ![secondEffectiveScale C D A K,normValue h,
    (Ideal.absNorm I:ℝ),(Ideal.absNorm J:ℝ)]
  have he : (∑ n : Blocks a b,((∏i : Fin 4,dyadicWeight (n i) (q i)):ℝ):ℝ)=1 :=
    dyadic_product_partition a b q ha hband
  calc
    _ = physicalKernel C D W K R (A*h) I J*(1:ℂ) := (mul_one _).symm
    _ = ∑ n : Blocks a b,physicalKernel C D W K R (A*h) I J*
        ((∏i : Fin 4,dyadicWeight (n i) (q i):ℝ):ℂ) := by
      rw [←Finset.mul_sum,←Complex.ofReal_sum,he,Complex.ofReal_one]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Fin.prod_univ_four]
      exact physical_kernel_dyadic C D I J hC hD hI hJ A h hA hh W K R hK (fun i=>n i)

end SevenEighths.CenteredMomentSecondDyadicPartition

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondRetainedRows
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondRetainedRows
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSecondSectorFrequency CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

theorem retained_mem_rows (R : ℝ) (A h : O) (hA : A≠0)
    (hh : retainedWeight R (normValue (A*h))≠0) : h∈retainedRows R A := by
  have he := retainedWeight_enclosure R _ hh
  have hAh : A*h≠0 := by
    intro hz
    have hn : normValue (A*h)=0 := by simp [hz,normValue]
    linarith [he.1]
  have hh0 : h≠0 := right_ne_zero_of_mul hAh
  apply mem_rowNormDisk.mpr
  constructor
  · have hn := normValue_pos h hh0
    unfold normValue at hn
    exact_mod_cast hn
  · have hbound : normValue h≤4*R/normValue A := by
      apply (le_div_iff₀ (normValue_pos A hA)).mpr
      simpa only [normValue_mul,mul_comm] using he.2
    have hb := hbound.trans (Nat.le_ceil (4*R/normValue A))
    unfold normValue at hb
    exact_mod_cast hb

theorem physical_sector_zero_of_weight (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (j : O)
    (hj : retainedWeight R (normValue j)=0) :
    sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) j=0 := by
  simp only [sectorFrequency,physicalKernel,hj,Complex.ofReal_zero,mul_zero,zero_mul,Finset.sum_const_zero]

theorem physical_partition_finite_rows (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (A : O) (hA : A≠0) (part : O→Prop) :
    (∑' h : O,if part h then
      sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑ h∈retainedRows R A,if part h then
        sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0 := by
  apply tsum_eq_sum
  intro h hh
  by_cases hp : part h
  · rw [if_pos hp]
    apply physical_sector_zero_of_weight η t S β C D hC hD W K R (A*h)
    by_contra hn
    exact hh (retained_mem_rows R A h hA hn)
  · rw [if_neg hp]

theorem actual_GV_finite_rows (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) :
    let A := commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
    (∑' h : O,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
      sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑ h∈retainedRows R A,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
        sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0 := by
  dsimp only
  exact physical_partition_finite_rows η t S β C D hC hD W K R _
    (mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
      (nonunitFrequencyGenerator_ne_zero C D hC U)) _

end SevenEighths.CenteredMomentSecondRetainedRows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondActiveDyadic
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondActiveDyadic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorColumns CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicPartition CenteredMomentSecondWholeKernel CenteredMomentLogDyadic CenteredMomentSmooth
open CenteredMomentActiveSource CenteredMomentSourceRow CenteredMomentSecondRetainedRows
local notation "O" => ActualEisensteinCubic.O

theorem active_sector_norm (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (H : ℝ) (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C : Ideal O) (hC : C≠0) (I : sectorPool C hC (activeSource S β)) :
    (Ideal.absNorm (I:Ideal O):ℝ)∈Set.Icc 1 (max 1 (H/(Ideal.absNorm C:ℝ))) := by
  have hh := residualPool_data S β H hH C hC I (Finset.mem_filter.mp I.property).1
  exact ⟨hh.2.2.2.2.1,hh.2.2.2.2.2.trans (le_max_right _ _)⟩

theorem sourceLower_pos (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (A : O) (hA : A≠0) (K : ℝ) (hK : 0<K) : ∀i,0<sourceLower C D A K i := by
  intro i
  fin_cases i
  · exact secondEffectiveScale_pos C D hC hD A hA K hK
  all_goals norm_num [sourceLower]

theorem active_physical_kernel_partition (_η : Character)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (H : ℝ)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (I : sectorPool C hC.1 (activeSource S β)) (J : sectorPool D hD.1 (activeSource S β))
    (A h : O) (hA : A≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    physicalKernel C D W K R (A*h) I J=
      ∑ n : Blocks (sourceLower C D A K) (sourceUpper C D A K R H),
        dyadicKernel C D A W K R (fun i=>n i) h I J := by
  by_cases hw : retainedWeight R (normValue (A*h))=0
  · simp only [physicalKernel,dyadicKernel,hw,Complex.ofReal_zero,mul_zero,zero_mul,Finset.sum_const_zero]
  have he := retainedWeight_enclosure R _ hw
  have hh : h≠0 := by
    intro hz
    subst h
    simp [normValue] at he
  have hrow : normValue h≤4*R/normValue A := by
    apply (le_div_iff₀ (normValue_pos A hA)).mpr
    simpa only [normValue_mul,mul_comm] using he.2
  have hb : ∀i, (![secondEffectiveScale C D A K,normValue h,
      (Ideal.absNorm (I:Ideal O):ℝ),(Ideal.absNorm (J:Ideal O):ℝ)] : Fin 4→ℝ) i∈
        Set.Icc (sourceLower C D A K i) (sourceUpper C D A K R H i) := by
    intro i
    fin_cases i
    · exact ⟨le_rfl,le_rfl⟩
    · exact ⟨normValue_ge_one h hh,hrow.trans (le_max_right _ _)⟩
    · exact active_sector_norm S β H hH C hC.1 I
    · exact active_sector_norm S β H hH D hD.1 J
  exact physical_kernel_dyadic_partition C D I J hC hD
    (sectorPool_supported C hC.1 _ I) (sectorPool_supported D hD.1 _ J)
    A h hA hh W K R hK _ _ (sourceLower_pos C D hC.1 hD.1 A hA K hK) hb

end SevenEighths.CenteredMomentSecondActiveDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondBlockAggregate
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondBlockAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentCanonicalFirst
open CenteredMomentSecondLocalization CenteredMomentSecondSectorFrequency
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorColumns
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentHeckeColumnWindow
open CenteredMomentSectorLocalization CenteredMomentActiveSource
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondRetainedRows
open CenteredMomentSecondActiveDyadic CenteredMomentSecondDyadicPartition
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondPhysicalBlock CenteredMomentSecondWholeKernel
local notation "O" => ActualEisensteinCubic.O

lemma retainedRows_ne_zero (R : ℝ) (A z : O) (hz : z∈retainedRows R A) : z≠0 := by
  have hp := (mem_rowNormDisk.mp hz).1
  intro h
  simp [h] at hp

theorem active_kernel_windows (η : Character)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (H : ℝ)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (I : sectorPool C hC.1 (activeSource S β)) (J : sectorPool D hD.1 (activeSource S β))
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    physicalKernel C D W K R (A*h) I J=
      ∑ n : Blocks (sourceLower C D A K) (sourceUpper C D A K R H),
        physicalKernel C D W K R (A*h) I J*
          ((dyadicWeight (n 0) (secondEffectiveScale C D A K)*dyadicWeight (n 1) (normValue h)*
            dyadicWeight (n 2) (Ideal.absNorm (I:Ideal O):ℝ)*
            dyadicWeight (n 3) (Ideal.absNorm (J:Ideal O):ℝ):ℝ):ℂ) := by
  refine (active_physical_kernel_partition η S β H hH C D hC hD I J A h hA W K R hK).trans ?_
  apply Finset.sum_congr rfl
  intro n hn
  exact (physical_kernel_dyadic C D I J hC hD
    (sectorPool_supported C hC.1 _ I) (sectorPool_supported D hD.1 _ J)
    A h hA hh W K R hK (fun i=>n i)).symm

theorem sector_finite_blocks (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (H : ℝ)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
    (∑h∈retainedRows R A,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
      sectorFrequency η t (activeSource S β) β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑n : SourceBlocks C D U K R H,
        physicalBlock η t (activeSource S β) β C D hC hD U R (retainedRows R A) W K
          (fun i=>(n i:ℤ)) := by
  dsimp only
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 :=
    mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
      (nonunitFrequencyGenerator_ne_zero C D hC U)
  unfold physicalBlock
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hp : canonicalPartition C D U (nonunitFrequencyGenerator C D U*h)
  · simp only [hp,ite_true]
    unfold sectorFrequency
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I hI
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro J hJ
    conv_lhs => rw [active_kernel_windows η S β H hH C D hC hD I J _ h hA
      (retainedRows_ne_zero R _ h hh) W K R hK,Finset.mul_sum]
  · simp only [hp,ite_false,Finset.sum_const_zero]

theorem original_secondRetainedEnergy_blocks (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ H : ℝ) (hK : 0<K)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H) :
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑p : ActiveLabel S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
        ∑U : Finset (CommonIndex p.val.1 p.val.2),
          ∑n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
            physicalBlock η t (activeSource S β) β p.val.1 p.val.2
              (commonLabels_supported (activeSource S β) _ _ p.property).1
              (commonLabels_supported (activeSource S β) _ _ p.property).2 U
              (frequencyRadius Tsec Z ξ)
              (retainedRows (frequencyRadius Tsec Z ξ)
                (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U))
              W K (fun i=>(n i:ℤ)) := by
  rw [←secondRetainedEnergy_active η t S β W K Tsec Z ξ,
    original_retained_energy_GV η t (activeSource S β) β W K Tsec Z ξ hK]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [actual_GV_finite_rows]
  exact sector_finite_blocks η t S β H hH _ _ _ _ U W K _ hK

end SevenEighths.CenteredMomentSecondBlockAggregate

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondRetainedWidth
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology

namespace SevenEighths.CenteredMomentSecondRetainedWidth
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondRadicalBudget CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondHeightFamily CenteredMomentChildRows CenteredMomentCanonicalFirst
open CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem retained_geometry (R : ℝ) (G V z : O)
    (hne : retainedWeight R (normValue ((G*V)*z))≠0) :
    0<R ∧ G≠0 ∧ V≠0 ∧ z≠0 ∧ 1≤normValue z ∧
      normValue z≤4*R/(normValue G*normValue V) ∧
      1≤4*R/(normValue G*normValue V) := by
  obtain ⟨hGV,hz⟩:=retained_product_ne_zero R (G*V) z hne
  have hg:=left_ne_zero_of_mul hGV
  have hv:=right_ne_zero_of_mul hGV
  have hrow:=retained_norm_enclosure R (G*V) z hGV hne
  rw [normValue_mul] at hrow
  have hn:=normValue_ge_one z hz
  have hr:=retainedWeight_enclosure R _ hne
  refine ⟨by linarith,hg,hv,hz,hn,hrow,hn.trans hrow⟩

end SevenEighths.CenteredMomentSecondRetainedWidth

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondLiveBlock
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondLiveBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorRetained
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLocalization CenteredMomentActiveSource
local notation "O" => HeckeFamily.O

lemma mem_liveLabels (η:Character) (S:Finset (Ideal O)) (β:Ideal O→ℂ) (p:ActiveLabel S β):
    p∈liveLabels η S β ↔ idealCoeff η p.val.1≠0 ∧ idealCoeff η p.val.2≠0:=by
  simp only [liveLabels,Finset.mem_filter,Finset.mem_univ,true_and]

lemma common_height_zero_of_not_live (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (p:ActiveLabel S β)
    (hp:p∉liveLabels η S β):heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)=0:=by
  rw [mem_liveLabels] at hp
  push Not at hp
  by_cases hc:idealCoeff η p.val.1=0
  · simp only [heightCoeff,hc,zero_mul]
  · simp only [heightCoeff,hp hc,zero_mul,star_zero,mul_zero]

lemma liveRows_weight (C D:Ideal O) (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O)
    (z:O) (hz:z∈liveRows C D U R rows):
    retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0:=
  (Finset.mem_filter.mp hz).2

lemma liveRows_geometry (C D:Ideal O) (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O)
    (z:O) (hz:z∈liveRows C D U R rows):
    0<R ∧ z≠0 ∧ 1≤normValue z ∧ normValue z≤
      4*R/(normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U)):=by
  obtain ⟨hr,hg,hv,hz0,h1,hbound,hmax⟩:=CenteredMomentSecondRetainedWidth.retained_geometry R
    (commonFrequencyGenerator C D) (nonunitFrequencyGenerator C D U) z
    (liveRows_weight C D U R rows z hz)
  exact ⟨hr,hz0,h1,hbound⟩

lemma physicalBlock_live_rows (η:Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (C D:Ideal O) (hC:Supported C) (hD:Supported D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n:=by
  unfold physicalBlock liveRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hr:retainedWeight R
      (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))=0
  · simp only [hr,ne_eq,not_true_eq_false,physicalKernel,Complex.ofReal_zero,
      mul_zero,zero_mul,Finset.sum_const_zero,ite_self]
  · simp only [hr,ne_eq,not_false_eq_true,ite_true]

theorem original_live_blocks (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (W:𝓢(ℝ,ℂ))
    (K Tsec Z ξ H:ℝ) (hK:0<K)
    (hH:∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H):
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑p∈liveLabels η S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
        ∑U:Finset (CommonIndex p.val.1 p.val.2),
          ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
            physicalBlock η t (activeSource S β) β p.val.1 p.val.2
              (commonLabels_supported (activeSource S β) _ _ p.property).1
              (commonLabels_supported (activeSource S β) _ _ p.property).2 U
              (frequencyRadius Tsec Z ξ)
              (liveRows p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ)
                (retainedRows (frequencyRadius Tsec Z ξ)
                  (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U)))
              W K (fun i=>(n i:ℤ)):=by
  rw [original_secondRetainedEnergy_blocks η t S β W K Tsec Z ξ H hK hH]
  trans ∑p∈liveLabels η S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
    ∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        physicalBlock η t (activeSource S β) β p.val.1 p.val.2
          (commonLabels_supported (activeSource S β) _ _ p.property).1
          (commonLabels_supported (activeSource S β) _ _ p.property).2 U
          (frequencyRadius Tsec Z ξ)
          (retainedRows (frequencyRadius Tsec Z ξ)
            (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U))
          W K (fun i=>(n i:ℤ))
  · symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p hp hn
    rw [common_height_zero_of_not_live η t S β p hn,zero_mul]
  · apply Finset.sum_congr rfl
    intro p hp
    apply congrArg (fun x : ℂ => heightCoeff η t p.val.1 * star (heightCoeff η t p.val.2) * x)
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro n hn
    exact physicalBlock_live_rows _ _ _ _ _ _ _ _ _ _ _ _ _ _

end SevenEighths.CenteredMomentSecondLiveBlock

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondEnergySplit
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLocalization CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentRestrictedEnergy
open CenteredMomentChildRows RayFourExpansion
local notation "O"=>HeckeFamily.O

lemma physicalBlock_filter_split (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)(p:O→Prop):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (rows.filter p) W K n+
      physicalBlock η t S β C D hC hD U R (rows.filter (fun z=>¬p z)) W K n:=by
  unfold physicalBlock
  exact (Finset.sum_filter_add_sum_filter_not rows p _).symm

lemma sourceRows_nonzero (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ)
    (z:O)(hz:z∈sourceRows C D U R):z≠0:=
  (liveRows_geometry C D U R _ z hz).2.1

lemma partRows_false (η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ):
    partRows false η χ Q m C D U R=(sourceRows C D U R).filter (fun z=>
      ¬CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z):=by
  ext z
  simp only [partRows,Bool.false_eq_true,ite_false,Finset.mem_filter,nonexceptional]
  exact ⟨fun h=>⟨h.1,h.2.2⟩,fun h=>⟨h.1,sourceRows_nonzero C D U R z h.1,h.2⟩⟩

theorem original_energy_split_oai (η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K Tsec Z ξ H:ℝ)(hK:0<K)
    (hH:∀I∈S,β I≠0→(I.absNorm:ℝ)≤H):
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      partEnergy true η χ Q m t S β W K Tsec Z ξ H+
      partEnergy false η χ Q m t S β W K Tsec Z ξ H:=by
  rw [original_live_blocks η t S β W K Tsec Z ξ H hK hH]
  unfold partEnergy
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [partRows_false]
  exact physicalBlock_filter_split η t (activeSource S β) β p.val.1 p.val.2 _ _ U
    (frequencyRadius Tsec Z ξ) (sourceRows p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ)) W K _ _

end SevenEighths.CenteredMomentSecondEnergySplit

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.CenteredMomentSecondEnergySplit.original_energy_split_oai := @OAI.SevenEighths.CenteredMomentSecondEnergySplit.original_energy_split_oai
