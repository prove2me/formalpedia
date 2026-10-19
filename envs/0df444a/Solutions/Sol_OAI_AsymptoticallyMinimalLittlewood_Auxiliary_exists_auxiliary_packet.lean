-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Auxiliary.exists_auxiliary_packet
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:36:12.769148+00:00
-- url     : https://prove2.me/submissions/155f1823-280e-4abb-b828-a9493f592da7

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Spreading.lean:L539-L714
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Auxiliary.exists_auxiliary_packet. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Auxiliary_binary_abs_le
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Auxiliary_binary_coefficients_energy
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Auxiliary_coeff_finite_sum
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Auxiliary_exists_binary_energy
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Auxiliary_spread_trunc_eventual_bound
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Curvature_determinant_tuning
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Cutoff_unit_cutoff
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_circleChirp_coefficient
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_circleChirp_mass
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_row_mass_error
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Spreading_quadratic_norm_scaled

-- ---- from OAI.Analysis.Littlewood.BinaryPacket ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uX

namespace AsymptoticallyMinimalLittlewood
namespace Auxiliary
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ComplexConjugate ENNReal
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instMeasureSpaceUnitAddCircle_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsAddHaarMeasureUnitAddCircleVolume_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsProbabilityMeasureUnitAddCircleVolume_oAI
lemma cosine_cast (x : UnitAddCircle) :
    (cosine x : ℂ) = (fourier 1 x + fourier (-1) x)/2 := by
  rw [fourier_neg]
  apply Complex.ext <;> simp [cosine]

lemma energy_bounds (n : ℕ) : 0 ≤ energy n ∧ energy n ≤ 1 := by
  refine ⟨integral_nonneg (fun x ↦ sq_nonneg _), ?_⟩
  calc
    energy n ≤ ∫ _ : Fin n → UnitAddCircle, (1:ℝ) := by
      apply integral_mono (((binary_continuous n).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (integrable_const _)
      intro x
      exact (sq_le_one_iff_abs_le_one _).mpr (binary_abs_le n x)
    _ = 1 := by simp

open UnitAddTorus

lemma spectrumSpan_mono {n : ℕ} {P Q : (Fin n → ℤ) → Prop} (h : ∀ s, P s → Q s) :
    spectrumSpan P ≤ spectrumSpan Q := by
  apply Submodule.span_mono
  rintro _ ⟨s,hs,rfl⟩
  exact ⟨s,h s hs,rfl⟩

lemma character_mem {n : ℕ} {P : (Fin n → ℤ) → Prop} {s : Fin n → ℤ} (h : P s) :
    (mFourier s : (Fin n → UnitAddCircle) → ℂ) ∈ spectrumSpan P :=
  Submodule.subset_span ⟨s,h,rfl⟩

lemma character_cons {n : ℕ} (k : ℤ) (s : Fin n → ℤ) (x : Fin (n+1) → UnitAddCircle) :
    mFourier (Fin.cons k s) x = fourier k (x 0)*mFourier s (Fin.tail x) := by
  simp [mFourier, Fin.prod_univ_succ, Fin.tail]

lemma spectrumSpan_lift {n : ℕ} {P : (Fin n → ℤ) → Prop}
    {Q : (Fin (n+1) → ℤ) → Prop} (k : ℤ)
    (h : ∀ s, P s → Q (Fin.cons k s)) {f : (Fin n → UnitAddCircle) → ℂ}
    (hf : f ∈ spectrumSpan P) :
    (fun x : Fin (n+1) → UnitAddCircle ↦ fourier k (x 0)*f (Fin.tail x)) ∈ spectrumSpan Q := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s,hs,rfl⟩ := hf
    simpa only [← character_cons] using character_mem (h s hs)
  | zero =>
    simp only [Pi.zero_apply, mul_zero]
    exact (spectrumSpan Q).zero_mem
  | add f g hf hg ihf ihg =>
    convert (spectrumSpan Q).add_mem ihf ihg using 1
    ext x
    simp [mul_add]
  | smul a f hf ih =>
    convert (spectrumSpan Q).smul_mem a ih using 1
    ext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

lemma allSpectrum_mul {n : ℕ} {f g : (Fin n → UnitAddCircle) → ℂ}
    (hf : f ∈ spectrumSpan (fun _ ↦ True)) (hg : g ∈ spectrumSpan (fun _ ↦ True)) :
    f*g ∈ spectrumSpan (fun _ ↦ True) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s,_,rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨t,_,rfl⟩ := hg
      convert character_mem (P := fun _ ↦ True) (s := s+t) trivial using 1
      ext x
      exact (mFourier_add).symm
    | zero => simp
    | add g h hg hh ihg ihh => simpa [mul_add] using (spectrumSpan (n := n) (fun _ ↦ True)).add_mem ihg ihh
    | smul a g hg ih => simpa [mul_smul_comm] using (spectrumSpan (n := n) (fun _ ↦ True)).smul_mem a ih
  | zero => simp
  | add f h hf hh ihf ihh => simpa [add_mul] using (spectrumSpan (n := n) (fun _ ↦ True)).add_mem ihf ihh
  | smul a f hf ih => simpa [smul_mul_assoc] using (spectrumSpan (n := n) (fun _ ↦ True)).smul_mem a ih

lemma allSpectrum_one (n : ℕ) : (1 : (Fin n → UnitAddCircle) → ℂ) ∈ spectrumSpan (fun _ ↦ True) := by
  simpa only [mFourier_zero, ContinuousMap.coe_one] using
    character_mem (P := fun _ ↦ True) (s := (0 : Fin n → ℤ)) trivial

lemma binary_spectrum (n : ℕ) :
    (fun x : Fin n → UnitAddCircle ↦ (binary n x : ℂ)) ∈ spectrumSpan (primitive n) := by
  induction n with
  | zero =>
    simp only [binary, Complex.ofReal_zero]
    exact (spectrumSpan (primitive 0)).zero_mem
  | succ n ih =>
    have ho := spectrumSpan_lift (Q := primitive (n+1)) 0
      (fun s hs ↦ by simp [primitive, hs]) ih
    have ha := spectrumSpan_mono (Q := fun _ ↦ True) (fun _ _ ↦ trivial) ih
    have hn := (spectrumSpan (n := n) (fun _ ↦ True)).sub_mem (allSpectrum_one n) (allSpectrum_mul ha ha)
    have hp := spectrumSpan_lift (Q := primitive (n+1)) 1 (fun s hs ↦ by simp [primitive]) hn
    have hm := spectrumSpan_lift (Q := primitive (n+1)) (-1) (fun s hs ↦ by simp [primitive]) hn
    convert (spectrumSpan (primitive (n+1))).add_mem ho
      ((spectrumSpan (primitive (n+1))).smul_mem (1/4:ℂ)
        ((spectrumSpan (primitive (n+1))).add_mem hp hm)) using 1
    ext x
    simp only [binary, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_ofNat,
      Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.one_apply, Pi.smul_apply, fourier_zero,
      one_mul, smul_eq_mul, cosine_cast]
    ring

lemma primitive_ne_zero {n : ℕ} {s : Fin n → ℤ} (h : primitive n s) : s ≠ 0 := by
  induction n with
  | zero => exact h.elim
  | succ n ih =>
    intro hs
    subst hs
    simp only [primitive, Pi.zero_apply, zero_ne_one, false_or] at h
    rcases h with h | ⟨_,h⟩
    · norm_num at h
    · exact ih h rfl

lemma primitive_parallel_scalar {n : ℕ} {s t : Fin n → ℤ}
    (hs : primitive n s) (ht : primitive n t) {c : ℝ}
    (he : ∀ i, (s i : ℝ) = c*(t i : ℝ)) : c=1 ∨ c = -1 := by
  have hc : c ≠ 0 := by
    intro hc
    apply primitive_ne_zero hs
    ext i
    exact_mod_cast (by simpa [hc] using he i : (s i : ℝ) = 0)
  induction n with
  | zero => exact hs.elim
  | succ n ih =>
    by_cases ht0 : t 0 = 0
    · have hs0 : s 0 = 0 := by exact_mod_cast (by simpa [ht0] using he 0 : (s 0 : ℝ) = 0)
      have hs' : primitive n (Fin.tail s) := by simpa [primitive, hs0] using hs
      have ht' : primitive n (Fin.tail t) := by simpa [primitive, ht0] using ht
      exact ih hs' ht' (fun i ↦ he i.succ)
    · have hs0 : s 0 ≠ 0 := by
        intro hs0
        have hz := he 0
        rw [hs0, Int.cast_zero] at hz
        have htR : (t 0 : ℝ) ≠ 0 := by exact_mod_cast ht0
        exact (mul_ne_zero hc htR) hz.symm
      have htsign : t 0 = 1 ∨ t 0 = -1 := by
        rcases ht with h | h | ⟨h,_⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact (ht0 h).elim
      have hssign : s 0 = 1 ∨ s 0 = -1 := by
        rcases hs with h | h | ⟨h,_⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact (hs0 h).elim
      rcases htsign with h | h <;> rcases hssign with h' | h'
      all_goals have hz := he 0; norm_num [h,h'] at hz; first | left; linarith | right; linarith

lemma exists_binary_coefficients (n : ℕ) :
    ∃ c : (Fin n → ℤ) →₀ ℂ, (∀ s ∈ c.support, primitive n s) ∧
      ∀ x, (binary n x : ℂ) = ∑ s ∈ c.support, c s*mFourier s x := by
  classical
  obtain ⟨c,hc,he⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).mp (binary_spectrum n)
  refine ⟨c, ?_, ?_⟩
  · exact fun s hs ↦ ((Finsupp.mem_supported ℂ c).mp hc) hs
  · intro x
    have hh := congrFun he x
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, smul_eq_mul] using hh.symm

lemma coeff_real_neg {n : ℕ} (f : (Fin n → UnitAddCircle) → ℝ) (s : Fin n → ℤ) :
    mFourierCoeff (fun x ↦ (f x : ℂ)) (-s) = conj (mFourierCoeff (fun x ↦ (f x : ℂ)) s) := by
  unfold mFourierCoeff
  trans ∫ x : Fin n → UnitAddCircle, conj (mFourier (-s) x*(f x : ℂ))
  · apply integral_congr_ae
    filter_upwards [] with x
    simp [mFourier_neg]
  · simpa only [smul_eq_mul] using! integral_conj

lemma positive_primitive {n : ℕ} {s : Fin n → ℤ} (h : positive n s) :
    primitive n s := by
  induction n with
  | zero => exact h.elim
  | succ n ih =>
    rcases h with h | ⟨h,ht⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨h,ih ht⟩)

lemma positive_not_neg {n : ℕ} {s : Fin n → ℤ} (h : positive n s) :
    ¬ positive n (-s) := by
  induction n with
  | zero => exact h.elim
  | succ n ih =>
    intro hn
    rcases h with h | ⟨h,ht⟩ <;> rcases hn with hn | ⟨hn,hnt⟩
    · simp [h] at hn
    · simp [h] at hn
    · simp [h] at hn
    · exact ih ht hnt

lemma primitive_positive_or_neg {n : ℕ} {s : Fin n → ℤ} (h : primitive n s) :
    positive n s ∨ positive n (-s) := by
  induction n with
  | zero => exact h.elim
  | succ n ih =>
    rcases h with h | h | ⟨h,ht⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl (by simp [h]))
    · rcases ih ht with hp | hp
      · exact Or.inl (Or.inr ⟨h,hp⟩)
      · exact Or.inr (Or.inr ⟨by simp [h],hp⟩)

lemma positive_parallel_eq {n : ℕ} {s t : Fin n → ℤ}
    (hs : positive n s) (ht : positive n t) {c : ℝ}
    (he : ∀ i, (s i : ℝ) = c*(t i : ℝ)) : s=t ∧ c=1 := by
  rcases primitive_parallel_scalar (positive_primitive hs) (positive_primitive ht) he with hc | hc
  · refine ⟨?_,hc⟩
    ext i
    exact_mod_cast (by simpa [hc] using he i : (s i : ℝ)=(t i : ℝ))
  · have hh : s = -t := by
      ext i
      exact_mod_cast (by simpa [hc] using he i : (s i : ℝ) = -(t i : ℝ))
    exact (positive_not_neg ht (hh ▸ hs)).elim

lemma binary_coefficients_conj {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ)
    (he : ∀ x, (binary n x : ℂ) = ∑ s ∈ c.support, c s*mFourier s x) (s : Fin n → ℤ) :
    c (-s) = conj (c s) := by
  have hf (t : Fin n → ℤ) : mFourierCoeff (fun x ↦ (binary n x : ℂ)) t = c t := by
    convert coeff_finite_sum c t using 1
    exact congrArg (fun g ↦ mFourierCoeff g t) (funext he)
  simpa only [hf] using coeff_real_neg (binary n) s

lemma binary_support_neg {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ)
    (he : ∀ x, (binary n x : ℂ) = ∑ s ∈ c.support, c s*mFourier s x) (s : Fin n → ℤ) :
    -s ∈ c.support ↔ s ∈ c.support := by
  simp only [Finsupp.mem_support_iff, binary_coefficients_conj c he, map_ne_zero]

lemma coefficient_support_pairs {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ)
    (hp : ∀ s ∈ c.support, primitive n s)
    (he : ∀ x, (binary n x : ℂ) = ∑ s ∈ c.support, c s*mFourier s x) :
    ∃ S : Finset (Fin n → ℤ), (∀ s ∈ S, positive n s) ∧
      ∀ s, s ∈ c.support ↔ s ∈ S ∨ -s ∈ S := by
  classical
  refine ⟨c.support.filter (positive n),?_,?_⟩
  · exact fun s hs ↦ (Finset.mem_filter.mp hs).2
  · intro s
    simp only [Finset.mem_filter, binary_support_neg c he, ← and_or_left]
    exact ⟨fun hs ↦ ⟨hs,primitive_positive_or_neg (hp s hs)⟩,fun h ↦ h.1⟩

end
end Auxiliary
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- from OAI.Analysis.Littlewood.Curvature ----
namespace OAI

universe uV uI

namespace AsymptoticallyMinimalLittlewood
namespace Curvature
noncomputable section
open scoped BigOperators Topology
open Filter

lemma exists_generic {I : Type uI} {V : Type uV} [Finite I] [AddCommGroup V] [Module ℝ V]
    (f : I → V →ₗ[ℝ] ℝ) (hf : ∀ i, f i ≠ 0) :
    ∃ x, ∀ i, f i x ≠ 0 := by
  apply Module.Dual.exists_forall_ne_zero_of_forall_exists
  intro i
  by_contra hn
  push Not at hn
  exact hf i (LinearMap.ext hn)

end
end Curvature
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- from OAI.Analysis.Littlewood.QuadraticTail ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
namespace OAI

universe uI uZ

namespace AsymptoticallyMinimalLittlewood
namespace QuadraticTail
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

lemma phase_smooth (t u : ℝ) : ContDiff ℝ ∞ (phase t u) := by
  have hc : ContDiff ℝ ∞ (fun x : ℝ ↦ 2*Real.pi*(t*x^2/2-u*x)) := by fun_prop
  exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ Complex.I)).mul
    (Complex.ofRealCLM.contDiff.comp hc)).cexp

lemma cutoff_zero {g : ℝ → ℂ} {α x : ℝ}
    (hs : tsupport g ⊆ Set.Icc (-α) α) (hx : x ∉ Set.Icc (-α) α) : g x=0 :=
  image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))

lemma circleChirp_continuous {g : ℝ → ℂ} (hg : Continuous g) {α : ℝ}
    (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α) (t : ℝ) :
    Continuous (circleChirp g t) := by
  apply AddCircle.liftIoc_continuous
  · have hleft : g (-1/2)=0 := cutoff_zero hs (by intro h; rcases h with ⟨h1,h2⟩; linarith)
    have hright : g (-1/2+1)=0 := cutoff_zero hs (by intro h; rcases h with ⟨h1,h2⟩; linarith)
    simp only [hleft,hright,zero_mul]
  · exact (hg.mul (phase_smooth t 0).continuous).continuousOn

lemma mem_box (T β : ℝ) (w : ℤ) :
    w ∈ box T β ↔ |(w:ℝ)| ≤ T*|β|/2 := by
  rw [box, Finset.mem_Icc, ← abs_le, ← Int.cast_abs, ← Int.le_floor]

lemma box_card_le {T : ℝ} (hT : 0≤T) (β : ℝ) :
    ((box T β).card : ℝ) ≤ T*|β|+1 := by
  have hfloor : 0 ≤ ⌊T*|β|/2⌋ := Int.floor_nonneg.mpr (by positivity)
  have hc := Int.card_Icc_of_le (-⌊T*|β|/2⌋) ⌊T*|β|/2⌋ (show -⌊T*|β|/2⌋ ≤ ⌊T*|β|/2⌋+1 by omega)
  have hcR : ((box T β).card : ℝ) = 2*(⌊T*|β|/2⌋ : ℝ)+1 := by
    simp only [box]
    exact_mod_cast (by omega : (Finset.Icc (-⌊T*|β|/2⌋) ⌊T*|β|/2⌋).card =
      (2*⌊T*|β|/2⌋+1 : ℤ))
  rw [hcR]
  linarith [Int.floor_le (T*|β|/2)]

lemma circle_parseval (f : C(UnitAddCircle,ℂ)) :
    HasSum (fun w : ℤ ↦ ‖fourierCoeff f w‖^2)
      (∫ z : UnitAddCircle, ‖f z‖^2 ∂AddCircle.haarAddCircle) := by
  have hh := hasSum_sq_fourierCoeff (f.toLp 2 AddCircle.haarAddCircle ℂ)
  simp only [fourierCoeff_toLp] at hh
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle] with x hx
  rw [hx]

end
end QuadraticTail
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- from OAI.Analysis.Littlewood.Spreading ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

namespace OAI

universe uI uE uJ uK

namespace AsymptoticallyMinimalLittlewood
namespace Spreading
noncomputable section
open QuadraticTail MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff FourierTransform SchwartzMap

variable {I : Type uI} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma determinant_pos {β : I → ℝ} (hβ : ∀ i, β i≠0) : 0<determinant β :=
  Finset.prod_pos (fun i _ ↦ abs_pos.mpr (hβ i))

lemma multiBox_card_bound {B : ℝ} (hB : 0<B) (β : I → ℝ) :
    ((multiBox B β).card : ℝ) ≤ B^(Fintype.card I) * ∏ i, (|β i|+1/B) := by
  rw [multiBox,Fintype.card_piFinset,Nat.cast_prod]
  calc
    _ ≤ ∏ i, (B*|β i|+1) := Finset.prod_le_prod₀ (fun i _ ↦ Nat.cast_nonneg _)
      (fun i _ ↦ box_card_le hB.le _)
    _ = ∏ i, B*(|β i|+1/B) := by
      apply Finset.prod_congr rfl
      intro i _
      field_simp
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

lemma multiBox_eventual_card {β : I → ℝ} (hβ : ∀ i, β i≠0)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ B : ℝ in atTop, ((multiBox B β).card : ℝ) ≤
      (1+ε)*B^(Fintype.card I)*determinant β := by
  have hd := determinant_pos hβ
  have hi : Tendsto (fun B : ℝ ↦ 1/B) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have hp : Tendsto (fun B : ℝ ↦ ∏ i, (|β i|+1/B)) atTop (𝓝 (determinant β)) := by
    simpa only [add_zero,determinant] using tendsto_finsetProd Finset.univ
      (fun i _ ↦ tendsto_const_nhds.add hi)
  have hg : ∀ᶠ B : ℝ in atTop, (∏ i, (|β i|+1/B)) ≤ (1+ε)*determinant β :=
    (hp.eventually (eventually_lt_nhds (by nlinarith : determinant β < (1+ε)*determinant β))).mono (fun _ h ↦ h.le)
  filter_upwards [hg,eventually_gt_atTop (0:ℝ)] with B hb hB
  calc
    _ ≤ B^(Fintype.card I)*(∏ i, (|β i|+1/B)) := multiBox_card_bound hB β
    _ ≤ B^(Fintype.card I)*((1+ε)*determinant β) := mul_le_mul_of_nonneg_left hb (pow_nonneg hB.le _)
    _ = _ := by ring

omit [DecidableEq I] in

lemma tensor_coefficient_eventual {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1) {β : I → ℝ}
    (hβ : ∀ i, β i≠0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ B : ℝ in atTop, ∀ u : I → ℤ,
      B^(Fintype.card I)*determinant β *
        ‖∏ i, (∫ x : ℝ, g x*phase (B*β i) (u i) x)‖^2 ≤ 1+ε := by
  choose C hC hc using (fun i ↦ quadratic_norm_scaled hg hgs hg1 (hβ i))
  have hi : Tendsto (fun B : ℝ ↦ 1/B) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have hp : Tendsto (fun B : ℝ ↦ ∏ i, (1+C i/B)^2) atTop (𝓝 1) := by
    have h (i : I) : Tendsto (fun B : ℝ ↦ (1+C i/B)^2) atTop (𝓝 1) := by
      have hci : Tendsto (fun B : ℝ ↦ C i/B) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.div_atTop tendsto_id)
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hci).pow 2
    simpa using tendsto_finsetProd Finset.univ (fun i _ ↦ h i)
  have hp' : ∀ᶠ B : ℝ in atTop, (∏ i, (1+C i/B)^2) ≤ 1+ε :=
    (hp.eventually (eventually_lt_nhds (by linarith : (1:ℝ) < 1+ε))).mono (fun _ h ↦ h.le)
  filter_upwards [hp',eventually_gt_atTop (0:ℝ)] with B hb hB
  intro u
  calc
    _ = ∏ i, (B*|β i| *‖∫ x : ℝ, g x*phase (B*β i) (u i) x‖^2) := by
      rw [norm_prod,← Finset.prod_pow]
      simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,determinant]
    _ ≤ ∏ i, (1+C i/B)^2 := Finset.prod_le_prod₀
      (fun i _ ↦ mul_nonneg (mul_nonneg hB.le (abs_nonneg _)) (sq_nonneg _))
      (fun i _ ↦ hc i B hB (u i))
    _ ≤ _ := hb

lemma row_mass_le {g : ℝ → ℂ} (hgs : Continuous g) {α : ℝ}
    (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α) (T β : ℝ) :
    (∑ w ∈ box T β, ‖∫ x : ℝ, g x*phase (T*β) w x‖^2) ≤
      ∫ x : ℝ, ‖g x‖^2 := by
  let f : C(UnitAddCircle,ℂ) := ⟨circleChirp g (T*β),circleChirp_continuous hgs hα hs _⟩
  have hp := circle_parseval f
  have hb := hp.summable.sum_le_tsum (box T β) (fun w _ ↦ sq_nonneg _)
  rw [hp.tsum_eq] at hb
  change (∑ w ∈ box T β, ‖fourierCoeff (circleChirp g (T*β)) w‖^2) ≤
    ∫ z : UnitAddCircle, ‖circleChirp g (T*β) z‖^2 ∂AddCircle.haarAddCircle at hb
  simpa only [circleChirp_coefficient hα hs,circleChirp_mass hα hs] using hb

lemma row_mass_tendsto {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1) {α : ℝ}
    (hα0 : 0≤α) (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α)
    {β : ℝ} (hβ : β≠0) :
    Tendsto (fun T : ℝ ↦ ∑ w ∈ box T β,
      ‖∫ x : ℝ, g x*phase (T*β) w x‖^2) atTop (𝓝 (∫ x : ℝ, ‖g x‖^2)) := by
  obtain ⟨C,hC,h⟩ := row_mass_error hg hgs hg1 hα0 hα hs hβ
  have hi : Tendsto (fun T : ℝ ↦ C/T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using tendsto_const_nhds.sub hi) tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT using h T hT
  · exact Eventually.of_forall (fun T ↦ row_mass_le hgs.continuous hα hs T β)

lemma tensor_mass_tendsto {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1) {α : ℝ}
    (hα0 : 0≤α) (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α)
    {β : I → ℝ} (hβ : ∀ i, β i≠0) :
    Tendsto (fun B : ℝ ↦ ∑ u ∈ multiBox B β,
      ‖∏ i, (∫ x : ℝ, g x*phase (B*β i) (u i) x)‖^2)
      atTop (𝓝 ((∫ x : ℝ, ‖g x‖^2)^(Fintype.card I))) := by
  have he (B : ℝ) : (∑ u ∈ multiBox B β,
      ‖∏ i, (∫ x : ℝ, g x*phase (B*β i) (u i) x)‖^2) =
      ∏ i, (∑ w ∈ box B (β i), ‖∫ x : ℝ, g x*phase (B*β i) w x‖^2) := by
    simp only [norm_prod,← Finset.prod_pow,multiBox]
    exact (Finset.prod_univ_sum (fun i : I ↦ box B (β i))
      (fun (i : I) (w : ℤ) ↦ ‖∫ x : ℝ, g x*phase (B*β i) w x‖^2)).symm
  simp_rw [he]
  simpa using tendsto_finsetProd Finset.univ
    (fun i _ ↦ row_mass_tendsto hg hgs hg1 hα0 hα hs (hβ i))

end
end Spreading
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood
namespace Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex

lemma support_pair_sum {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ)
    (S : Finset (Fin n → ℤ)) (hp : ∀ s ∈ S, positive n s)
    (hc : ∀ s, s ∈ c.support ↔ s ∈ S ∨ -s ∈ S)
    {E : Type uE} [AddCommMonoid E] (f : (Fin n → ℤ) → E) :
    ∑ s ∈ c.support, f s = ∑ s ∈ S, (f s+f (-s)) := by
  classical
  have hd : Disjoint S (S.image Neg.neg) := by
    rw [Finset.disjoint_left]
    intro s hs hn
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hn
    exact positive_not_neg (hp t ht) (hp _ hs)
  have he : c.support = S ∪ S.image Neg.neg := by
    ext s
    simpa only [Finset.mem_union, Finset.mem_image, neg_eq_iff_eq_neg,
      exists_eq_right] using hc s
  rw [he, Finset.sum_union hd, Finset.sum_image (by
    intro x _ y _ h; exact neg_injective h), Finset.sum_add_distrib]

lemma binary_positive_data {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) :
    ∃ n : ℕ, ∃ S : Finset (Fin n → ℤ), S.Nonempty ∧
      (∀ s ∈ S, positive n s) ∧ ∃ c : (Fin n → ℤ) → ℂ,
      (∀ s ∈ S, c s≠0) ∧
      (∀ x : Fin n → UnitAddCircle,
        (binary n x : ℂ) = (∑ s ∈ S, c s*mFourier s x) +
          conj (∑ s ∈ S, c s*mFourier s x)) ∧
      1-δ ≤ 2*∑ s ∈ S, ‖c s‖^2 ∧ 2*∑ s ∈ S, ‖c s‖^2 ≤ 1 := by
  classical
  obtain ⟨n,hn,he⟩ := exists_binary_energy hδ
  obtain ⟨c,hp,hc⟩ := exists_binary_coefficients n
  obtain ⟨S,hS,hSp⟩ := coefficient_support_pairs c hp hc
  have hm : 2*∑ s ∈ S, ‖c s‖^2 = energy n := by
    rw [← binary_coefficients_energy c hc, support_pair_sum c S hS hSp]
    simp only [binary_coefficients_conj c hc, norm_conj]
    rw [Finset.sum_add_distrib]
    ring
  have hSn : S.Nonempty := by
    by_contra hz
    have hz' : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hz
    rw [hz'] at hm
    simp only [Finset.sum_empty,mul_zero] at hm
    linarith
  refine ⟨n,S,hSn,hS,c,?_,?_,by linarith,by rw [hm]; exact (energy_bounds n).2⟩
  · intro s hs
    exact Finsupp.mem_support_iff.mp ((hSp s).mpr (Or.inl hs))
  · intro x
    rw [hc, support_pair_sum c S hS hSp, Finset.sum_add_distrib]
    congr 1
    simp only [map_sum,map_mul,binary_coefficients_conj c hc,mFourier_neg]

lemma rowForm_apply {n : ℕ} (s : Fin n → ℤ) (x : Fin n → ℝ) :
    rowForm s x = ∑ k, (s k : ℝ)*x k := by simp [rowForm]

lemma rowForm_injective {n : ℕ} : Function.Injective (@rowForm n) := by
  classical
  intro s t h
  ext k
  have hh := congrArg (fun f : (Fin n → ℝ) →ₗ[ℝ] ℝ ↦ f (Pi.single k 1)) h
  simp [rowForm_apply, Pi.single_apply, mul_ite] at hh
  exact_mod_cast hh

lemma positive_rowForm_ne_zero {n : ℕ} {s : Fin n → ℤ} (hs : positive n s) :
    rowForm s ≠ 0 := by
  intro hz
  apply primitive_ne_zero (positive_primitive hs)
  apply rowForm_injective
  simpa [rowForm] using hz

lemma positive_rowForm_nonparallel {n : ℕ} {s t : Fin n → ℤ}
    (hs : positive n s) (ht : positive n t) (hne : s ≠ t) (c : ℝ) :
    rowForm s ≠ c • rowForm t := by
  classical
  intro he
  apply hne
  apply (positive_parallel_eq hs ht (c := c) ?_).1
  intro k
  have hh := congrArg (fun f : (Fin n → ℝ) →ₗ[ℝ] ℝ ↦ f (Pi.single k 1)) he
  simpa [rowForm_apply, Pi.single_apply, mul_ite] using hh

end
end Auxiliary
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

lemma tensor_trunc_expand {J : Type uJ} [Fintype J] [DecidableEq J]
    (g : ℝ → ℂ) (B : ℝ) (β : J → ℝ) (z : J → UnitAddCircle) :
    (∏ j, rowTrunc g B (β j) (z j)) =
      ∑ u∈multiBox B β, (∏ j, ∫ x : ℝ, g x*phase (B*β j) (u j) x)*mFourier u z := by
  classical
  simp only [rowTrunc,multiBox,mFourier,ContinuousMap.coe_mk,← Finset.prod_mul_distrib]
  exact Finset.prod_univ_sum _ _

lemma cutoff_power {D : ℕ} {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∃ α : ℝ, 0<α ∧ α<1/2 ∧ tsupport g ⊆ Set.Icc (-α) α) ∧
      (∀ x, 0≤g x ∧ g x≤1) ∧
      1-δ < (∫ x : ℝ, g x^2)^D := by
  have hD : (0:ℝ)<D+1 := by positivity
  let ε : ℝ := δ/(D+1)
  have hε : 0<ε := div_pos hδ hD
  have hε1 : ε<1 := by dsimp [ε]; rw [div_lt_one hD]; have : (0:ℝ)≤D := Nat.cast_nonneg _; linarith
  obtain ⟨g,hgs,hgc,hga,hg,hm⟩ := Cutoff.unit_cutoff hε
  refine ⟨g,hgs,hgc,hga,hg,?_⟩
  have hb := one_add_mul_le_pow (a := -ε) (by linarith : (-2:ℝ)≤-ε) D
  have hp : (1-ε)^D ≤ (∫ x : ℝ, g x^2)^D := pow_le_pow_left₀ (by linarith) hm.le _
  have hi : (D : ℝ)*ε<δ := by dsimp [ε]; rw [← mul_div_assoc, div_lt_iff₀ hD]; nlinarith
  have hh : 1-δ < 1+(D:ℝ)*(-ε) := by linarith
  exact hh.trans_le (hb.trans (by simpa only [sub_eq_add_neg] using hp))

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

attribute [instance] FinitePacket.fintypeI FinitePacket.fintypeJ FinitePacket.nonemptyI

lemma mFourier_sum_type {J : Type uJ} {K : Type uK} [Fintype J] [Fintype K]
    (s : J → ℤ) (u : K → ℤ) (x : J ⊕ K → UnitAddCircle) :
    mFourier (Sum.elim s u) x = mFourier s (x ∘ Sum.inl)*mFourier u (x ∘ Sum.inr) := by
  simp only [mFourier,ContinuousMap.coe_mk,Fintype.prod_sum_type,Sum.elim_inl,
    Sum.elim_inr,Function.comp_apply]

lemma spread_numeric_coefficient {δ τ P Δ ρ U V : ℝ}
    (hδ : 0<δ) (hδ1 : δ<1) (hτ : 0<τ) (hP : 0<P) (hρ : 0<ρ)
    (_hU : 0≤U) (hV : 0≤V)
    (hdet : (1-δ)*τ*U/ρ ≤ Δ) (hdisc : P*Δ*V≤(1+δ)^2) :
    U*V/(1+δ)^2 ≤ ((1+δ)^3/(1-δ))*(ρ/(τ*P*(1+δ)^3)) := by
  have hd0 : 0<1-δ := sub_pos.mpr hδ1
  have hd1 : 0<1+δ := by linarith
  have hd2 := mul_le_mul_of_nonneg_right hdet (mul_nonneg hP.le hV)
  have hd3 := mul_le_mul_of_nonneg_left hdisc hρ.le
  have he : ((1-δ)*τ*U/ρ)*(P*V)*ρ=(1-δ)*τ*P*(U*V) := by field_simp
  have hd4 := mul_le_mul_of_nonneg_right hd2 hρ.le
  rw [he] at hd4
  have hraw : (1-δ)*τ*P*(U*V)≤ρ*(1+δ)^2 := by nlinarith only [hd3,hd4]
  have hr : ((1+δ)^3/(1-δ))*(ρ/(τ*P*(1+δ)^3))=ρ/((1-δ)*τ*P) := by
    field_simp
  rw [hr]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd1) (by positivity)).mpr
  nlinarith only [hraw]

lemma spread_numeric_width {δ τ P Δ ρ U L : ℝ}
    (hδ : 0<δ) (hτ : 0<τ) (hP : 0<P) (hρ : 0<ρ)
    (hdet : Δ ≤ (1+δ)*τ*U/ρ) (hcard : L≤(1+δ)*P*Δ) :
    L*(ρ/(τ*P*(1+δ)^3))≤U/(1+δ) := by
  have hd1 : 0<1+δ := by linarith
  have h1 := mul_le_mul_of_nonneg_left hdet (mul_nonneg hd1.le hP.le)
  have h2 := mul_le_mul_of_nonneg_right (hcard.trans h1) hρ.le
  have he : (1+δ)*P*((1+δ)*τ*U/ρ)*ρ=τ*P*(1+δ)^2*U := by field_simp
  rw [he] at h2
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) hd1).mpr
  have hh := mul_le_mul_of_nonneg_right h2 hd1.le
  nlinarith only [hh]

lemma spread_numeric_energy {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1/20) :
    (1-3*δ)^2 ≤ ((1-δ)*(1-2*δ))/(1+δ)^2 := by
  have h1 : 0≤1-3*δ := by linarith
  have h2 : 0≤1-2*δ := by linarith
  have hd : 0<1+δ := by linarith
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  have hh : (1-3*δ)*(1+δ)≤1-2*δ := by nlinarith [sq_nonneg δ]
  have hsq : ((1-3*δ)*(1+δ))^2≤(1-2*δ)^2 := sq_le_sq₀ (mul_nonneg h1 hd.le) h2 |>.mpr hh
  nlinarith [mul_nonneg hδ.le h2]

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

/-- The full Fourier-spreading construction, before adjoining a harmless zero
coefficient to ensure that the packing catalogue has at least two rows. -/
theorem exists_auxiliary_packet {δ : ℝ} (hδ : 0<δ) (hδ20 : δ<1/20) :
    Nonempty (FinitePacket δ) := by
  classical
  have hδ1 : δ<1 := by linarith
  have hd : 0<1+δ := by linarith
  obtain ⟨n,S,hSn,hS,c,hc,hpoly,hElo,hEhi⟩ := binary_positive_data hδ hδ1
  let I := ↥S
  have : Nonempty I := ⟨⟨hSn.choose,hSn.choose_spec⟩⟩
  let f : I → (Fin n → ℝ) →ₗ[ℝ] ℝ := fun i ↦ rowForm i.val
  have hf (i : I) : f i≠0 := positive_rowForm_ne_zero (hS i.val i.property)
  have hfp (i j : I) (hij : i≠j) (t : ℝ) : f i≠t • f j :=
    positive_rowForm_nonparallel (hS i.val i.property) (hS j.val j.property)
      (fun h ↦ hij (Subtype.ext h)) t
  obtain ⟨γ,hγ⟩ := Curvature.exists_generic f hf
  let ρ : I → ℝ := fun i ↦ |f i γ|
  have hρ (i : I) : 0<ρ i := abs_pos.mpr (hγ i)
  have hc0 (i : I) : 0<‖c i.val‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (hc i.val i.property))
  obtain ⟨τ,hτ,b,hb,hdet⟩ := Curvature.determinant_tuning f hf hfp
    (fun i ↦ ‖c i.val‖^2/ρ i) (fun i ↦ div_pos (hc0 i) (hρ i)) hδ hδ1
  let β : I → I → ℝ := fun i j ↦ f i (b j)
  have hβ (i j : I) : β i j≠0 := hb i j
  obtain ⟨g,hgs,hgc,⟨α,hα0,hα,hga⟩,hg,hgm⟩ := cutoff_power (D := Fintype.card I) hδ hδ1
  let g' : ℝ → ℂ := fun x ↦ (g x : ℂ)
  have hgs' : ContDiff ℝ ∞ g' := Complex.ofRealCLM.contDiff.comp hgs
  have hgc' : HasCompactSupport g' := hgc.comp_left (g := (Complex.ofReal : ℝ → ℂ)) (by simp)
  have hg' : ∀ x, ‖g' x‖≤1 := by
    intro x
    simpa [g',Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hg x).1] using (hg x).2
  have hga' : tsupport g' ⊆ Set.Icc (-α) α :=
    (tsupport_comp_subset (g := (Complex.ofReal : ℝ → ℂ)) (by simp) g).trans hga
  have hm' : 1-δ < (∫ x : ℝ, ‖g' x‖^2)^(Fintype.card I) := by
    simpa only [g',Complex.norm_real,Real.norm_eq_abs,sq_abs] using hgm
  have hcards : ∀ᶠ B : ℝ in atTop, ∀ i : I,
      ((multiBox B (β i)).card : ℝ)≤(1+δ)*B^(Fintype.card I)*determinant (β i) := by
    rw [Filter.eventually_all]
    exact fun i ↦ multiBox_eventual_card (hβ i) hδ
  have hε : 0<(1+δ)^2-1 := by nlinarith
  have hcoeffs : ∀ᶠ B : ℝ in atTop, ∀ i : I, ∀ u : I → ℤ,
      B^(Fintype.card I)*determinant (β i)*
        ‖∏ j, (∫ x : ℝ, g' x*phase (B*β i j) (u j) x)‖^2 ≤ (1+δ)^2 := by
    rw [Filter.eventually_all]
    intro i
    simpa only [add_sub_cancel] using tensor_coefficient_eventual hgc' hgs' hg' (hβ i) hε
  have hmasses : ∀ᶠ B : ℝ in atTop, ∀ i : I,
      1-2*δ ≤ ∑ u∈multiBox B (β i), ‖∏ j, (∫ x : ℝ, g' x*phase (B*β i j) (u j) x)‖^2 := by
    rw [Filter.eventually_all]
    intro i
    exact ((tensor_mass_tendsto hgc' hgs' hg' hα0.le hα hga' (hβ i)).eventually
      (eventually_gt_nhds (by linarith : 1-2*δ<(∫ x : ℝ, ‖g' x‖^2)^(Fintype.card I)))).mono (fun _ h ↦ h.le)
  have hbound := spread_trunc_eventual_bound S c hpoly hgs hgc hg hα0.le hα hga b
    (by intro s hs j; exact hb ⟨s,hs⟩ j) hδ
  obtain ⟨B,hBc,hBs,hBm,hBd,hB⟩ :=
    (hcards.and (hcoeffs.and (hmasses.and (hbound.and (eventually_ge_atTop (1:ℝ)))))).exists
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB
  let U (i : I) := multiBox B (β i)
  let Q := (i : I) × ↥(U i)
  let J := Fin n ⊕ I
  let A : Q → J → ℤ := fun q ↦ Sum.elim q.1.val q.2.val
  let T (i : I) (u : I → ℤ) : ℂ := ∏ j, (∫ x : ℝ, g' x*phase (B*β i j) (u j) x)
  let C : Q → ℂ := fun q ↦ c q.1.val*T q.1 q.2.val/(1+δ : ℂ)
  let P : ℝ := B^(Fintype.card I)
  have hP : 0<P := pow_pos hB0 _
  let den : ℝ := τ*P*(1+δ)^3
  have hden : 0<den := by dsimp [den]; positivity
  let v : J → ℝ := Sum.elim (fun k ↦ γ k/den) (fun _ ↦ 0)
  have hcurv (q : Q) : (∑ j, (A q j : ℝ)*v j)=f q.1 γ/den := by
    simp only [J,A,v,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,mul_zero,
      Finset.sum_const_zero,add_zero,← mul_div_assoc,← Finset.sum_div]
    simp only [f,rowForm_apply]
  have hwidth (q : Q) : |∑ j, (A q j : ℝ)*v j|=ρ q.1/den := by
    rw [hcurv,abs_div,abs_of_pos hden]
  have hC (q : Q) : ‖C q‖^2=‖c q.1.val‖^2*‖T q.1 q.2.val‖^2/(1+δ)^2 := by
    dsimp [C]
    rw [norm_div,norm_mul,div_pow,mul_pow]
    norm_cast
    rw [Real.norm_eq_abs,abs_of_pos hd]
  have hsum : (∑ q : Q, ‖C q‖^2)=
      (∑ i : I, ‖c i.val‖^2*(∑ u∈U i, ‖T i u‖^2))/(1+δ)^2 := by
    simp only [Q,Fintype.sum_sigma,hC]
    simp only [← Finset.sum_div,← Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (Finset.sum_subtype (U i) (fun _ ↦ Iff.rfl) (fun u ↦ ‖T i u‖^2)).symm
  have hElo' : 1-δ≤2*∑ i : I, ‖c i.val‖^2 := by
    simpa only [← Finset.sum_coe_sort S] using hElo
  have hEhi' : 2*∑ i : I, ‖c i.val‖^2≤1 := by
    simpa only [← Finset.sum_coe_sort S] using hEhi
  have helo : (1-3*δ)^2≤2*∑ q : Q, ‖C q‖^2 := by
    have h2 : 0≤1-2*δ := by linarith
    have hterm : (∑ i : I, ‖c i.val‖^2)*(1-2*δ)≤∑ i : I, ‖c i.val‖^2*(∑ u∈U i, ‖T i u‖^2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hBm i) (sq_nonneg _)
    have he := mul_le_mul_of_nonneg_right hElo' h2
    rw [hsum]
    apply (spread_numeric_energy hδ hδ20).trans
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by nlinarith only [hterm,he]) (sq_nonneg _)
  have hwterm (i : I) : ((U i).card : ℝ)*(ρ i/den)≤‖c i.val‖^2/(1+δ) := by
    apply spread_numeric_width hδ hτ hP (hρ i)
    · simpa only [determinant,β,mul_div_assoc] using (hdet i).2
    · exact hBc i
  have hwsum : 2*(∑ q : Q, |∑ j, (A q j : ℝ)*v j|)≤1/(1+δ) := by
    simp only [hwidth,Q,Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,Fintype.card_coe]
    calc
      _ ≤ 2*(∑ i : I, ‖c i.val‖^2/(1+δ)) := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ hwterm i)) (by norm_num)
      _ = (2*∑ i : I, ‖c i.val‖^2)/(1+δ) := by rw [← Finset.sum_div]; ring
      _ ≤ 1/(1+δ) := div_le_div_of_nonneg_right hEhi' hd.le
  have hsup (y : J → UnitAddCircle) :
      ‖(∑ q : Q, C q*mFourier (A q) y)+conj (∑ q : Q, C q*mFourier (A q) y)‖≤1 := by
    let Z : ℂ := ∑ s∈S, c s*mFourier s (y ∘ Sum.inl)*
      ∏ j : I, rowTrunc g' B (rowForm s (b j)) (y (Sum.inr j))
    have hZ : ‖Z+conj Z‖≤1+δ := hBd (y ∘ Sum.inl) (y ∘ Sum.inr)
    have he : (∑ q : Q, C q*mFourier (A q) y)=Z/(1+δ : ℂ) := by
      rw [Fintype.sum_sigma]
      have hi (i : I) : (∑ u : U i, C ⟨i,u⟩*mFourier (A ⟨i,u⟩) y)=
          (c i.val*mFourier i.val (y ∘ Sum.inl)*(∏ j : I, rowTrunc g' B (β i j) (y (Sum.inr j))))/(1+δ : ℂ) := by
        rw [tensor_trunc_expand]
        change (∑ u : U i, (c i.val*T i u.val/(1+δ : ℂ))*mFourier (Sum.elim i.val u.val) y)=_
        simp only [mFourier_sum_type,Finset.mul_sum,Finset.sum_div]
        rw [← Finset.sum_coe_sort (U i)]
        apply Finset.sum_congr rfl
        intro u _
        dsimp [T, Function.comp_def]
        ring
      simp_rw [hi]
      rw [← Finset.sum_div]
      congr 1
      simpa only [Z,β,f] using Finset.sum_coe_sort S
        (fun s ↦ c s*mFourier s (y ∘ Sum.inl)*∏ j : I, rowTrunc g' B (rowForm s (b j)) (y (Sum.inr j)))
    rw [he,map_div₀,map_add,map_one,conj_ofReal,← add_div,norm_div]
    have he' : ‖(1:ℂ)+(δ:ℂ)‖=1+δ := by
      rw [← Complex.ofReal_one,← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
    rw [he',div_le_one hd]
    exact hZ
  have hQ : Nonempty Q := by
    let i : I := Classical.choice inferInstance
    have hu : (0 : I → ℤ)∈U i := by
      simp only [U,multiBox,Fintype.mem_piFinset,Pi.zero_apply,mem_box,Int.cast_zero,abs_zero]
      intro j
      positivity
    exact ⟨⟨i,⟨0,hu⟩⟩⟩
  refine ⟨⟨Q,J,inferInstance,inferInstance,hQ,⟨A,C,v,?_,?_,hsup,helo,?_,?_,?_⟩⟩⟩
  · intro q hz
    apply primitive_ne_zero (positive_primitive (hS q.1.val q.1.property))
    funext k
    exact congrFun hz (Sum.inl k)
  · rintro ⟨s,u⟩ ⟨t,w⟩ hne a ha
    have hh := positive_parallel_eq (hS s.val s.property) (hS t.val t.property)
      (fun k ↦ ha (Sum.inl k))
    have hst : s=t := Subtype.ext hh.1
    subst t
    have huw : u=w := by
      apply Subtype.ext
      funext j
      have hj := ha (Sum.inr j)
      change (u.val j : ℝ)=a*(w.val j : ℝ) at hj
      rw [hh.2,one_mul] at hj
      exact_mod_cast hj
    exact hne (by rw [huw])
  · intro q
    rw [hcurv]
    exact div_ne_zero (hγ q.1) hden.ne'
  · apply hwsum.trans_lt
    exact (div_lt_one hd).mpr (by linarith)
  · intro q
    rw [hC,hwidth]
    apply spread_numeric_coefficient hδ hδ1 hτ hP (hρ q.1) (sq_nonneg _) (sq_nonneg _)
    · simpa only [determinant,β,mul_div_assoc] using (hdet q.1).1
    · exact hBs q.1 q.2.val

end
end AsymptoticallyMinimalLittlewood.Auxiliary

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Auxiliary
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Auxiliary.exists_auxiliary_packet := @_root_.OAI.AsymptoticallyMinimalLittlewood.Auxiliary.exists_auxiliary_packet
