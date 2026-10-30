-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketRepresentation.exists_normalized_symbol_basic_l1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:26:42.662772+00:00
-- url     : https://prove2.me/submissions/0b39fe26-ea62-4ab6-951a-3f0f1c414295

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_exists_universal_ordinary_model_estimate

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketPolarization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact four-term polarization of a cross packet coefficient and
synthesizing wave. Both packets may have different planar profiles. -/

noncomputable section
namespace LipschitzHilbert

theorem packet_cross_polarization (a b f g : ℂ) :
    (a+b)*(f+g) - (a-b)*(f-g) -
        Complex.I*((a-Complex.I*b)*(f+Complex.I*g)) +
        Complex.I*((a+Complex.I*b)*(f-Complex.I*g)) = 4*(a*g) := by
  ring_nf
  simp [Complex.I_sq]
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CoefficientPolarization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Antilinearity of the actual analyzing integral supplies the
coefficients in the four-term packet polarization identity. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert
variable {Ω σ κ : Type*} [MeasurableSpace Ω]

theorem analyzingCoefficient_add_smul (μ : Measure Ω) (area : σ → ℝ)
    (f h : σ → κ → Ω → ℂ) (g : Ω → EuclideanSpace ℂ κ) (c : ℂ)
    (hf : ∀ s k, Integrable (fun z => g z k*conj (f s k z)) μ)
    (hh : ∀ s k, Integrable (fun z => g z k*conj (h s k z)) μ) (s : σ) :
    analyzingCoefficient μ area (fun s k z => f s k z+c*h s k z) g s =
      analyzingCoefficient μ area f g s + conj c • analyzingCoefficient μ area h g s := by
  ext k
  change ((↑(area s) : ℂ)⁻¹)*(∫ z, g z k*conj (f s k z+c*h s k z) ∂μ) =
    ((↑(area s) : ℂ)⁻¹)*(∫ z, g z k*conj (f s k z) ∂μ) +
      conj c*(((↑(area s) : ℂ)⁻¹)*(∫ z, g z k*conj (h s k z) ∂μ))
  have heq : (fun z => g z k*conj (f s k z+c*h s k z)) =
      (fun z => g z k*conj (f s k z)+conj c*(g z k*conj (h s k z))) := by
    funext z
    simp only [map_add,map_mul]
    ring
  rw [heq,integral_add (hf s k) ((hh s k).const_mul (conj c)),integral_const_mul]
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SeparatedSymbolFourier
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separation of the normalized (X,Y,U) symbol by Fourier inversion.
The two frequency coordinates and the selector coordinate are separated
inside an absolutely convergent integral. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem symbolPoint_inner (nu : SymbolSpace) (X Y U : ℝ) :
    inner ℝ nu (symbolPoint X Y U)=nu 0*X+nu 1*Y+nu 2*U := by
  simp [PiLp.inner_apply, symbolPoint, Fin.sum_univ_succ]
  ring

theorem norm_frequencyCharacter (nu : SymbolSpace) (X Y : ℝ) :
    ‖frequencyCharacter nu X Y‖=1 := by
  simp only [frequencyCharacter, norm_mul, Circle.norm_coe, one_mul]

theorem norm_selectorCharacter (nu : SymbolSpace) (U : ℝ) :
    ‖selectorCharacter nu U‖=1 := Circle.norm_coe _

theorem separated_symbol_fourier (S : SchwartzMap SymbolSpace ℂ) (X Y U : ℝ) :
    S (symbolPoint X Y U)=∫ nu : SymbolSpace,
      𝓕 S nu * frequencyCharacter nu X Y * selectorCharacter nu U := by
  have hinv : (𝓕⁻ (𝓕 S : SchwartzMap SymbolSpace ℂ) : SchwartzMap SymbolSpace ℂ)=S :=
    FourierTransform.fourierInv_fourier_eq _
  have h := congrArg (fun f : SchwartzMap SymbolSpace ℂ => f (symbolPoint X Y U)) hinv
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq] at h
  calc
    _ = ∫ nu : SymbolSpace, Real.fourierChar (inner ℝ nu (symbolPoint X Y U)) • 𝓕 S nu := h.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with nu
      rw [symbolPoint_inner, Real.fourierChar.map_add_eq_mul, Real.fourierChar.map_add_eq_mul]
      simp only [Circle.smul_def, Circle.coe_mul, smul_eq_mul, frequencyCharacter, selectorCharacter]
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SymbolWeights
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrable fixed polynomial weights for the separated symbol.
The same weight is allocated to the two waves and to the selector,
leaving an integrable outside coefficient. Only a fixed seminorm is used. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem symbolWeight_pos (q : ℕ) (nu : SymbolSpace) : 0 < symbolWeight q nu :=
  inv_pos.mpr (pow_pos (by positivity) q)

theorem symbolWeight_integrable (q : ℕ) (hq : 4≤q) : Integrable (symbolWeight q) := by
  have hi : Integrable (fun nu : SymbolSpace => (1+‖nu‖)^(-(q:ℝ))) :=
    integrable_one_add_norm (by simp only [SymbolSpace, finrank_euclideanSpace_fin]; exact_mod_cast (by omega : 3<q))
  apply hi.congr
  filter_upwards [] with nu
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  rfl

theorem symbolCoefficientBound_pos (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) :
    0 < symbolCoefficientBound S q := by unfold symbolCoefficientBound; positivity

theorem symbol_coefficient_decay (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (nu : SymbolSpace) :
    ‖𝓕 S nu‖ ≤ symbolCoefficientBound S q*(symbolWeight q nu)^4 := by
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (4*q,0)) (k := 4*q) (n := 0) le_rfl le_rfl (𝓕 S) nu
  have h0 : ‖iteratedFDeriv ℝ 0 (𝓕 S : SchwartzMap SymbolSpace ℂ) nu‖=‖𝓕 S nu‖ := by simp
  rw [h0] at h
  have hr : 0<1+‖nu‖ := by positivity
  have hp : (symbolWeight q nu)^4=((1+‖nu‖)^(4*q))⁻¹ := by
    simp only [symbolWeight, inv_pow, ← pow_mul, Nat.mul_comm]
  rw [hp, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hr _)).2
  unfold symbolCoefficientBound
  linarith only [h]

theorem weightedSelector_bound (S : SchwartzMap SymbolSpace ℂ) (q : ℕ)
    (nu : SymbolSpace) (U : ℝ) :
    ‖weightedSelector S q nu U‖ ≤ symbolCoefficientBound S q*symbolWeight q nu := by
  have hw := symbolWeight_pos q nu
  have hwc : ‖(symbolWeight q nu : ℂ)‖=symbolWeight q nu := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
  rw [weightedSelector, norm_mul, norm_selectorCharacter, mul_one, norm_div, norm_pow, hwc]
  apply (div_le_iff₀ (pow_pos hw 3)).2
  exact (symbol_coefficient_decay S q nu).trans_eq (by ring)

theorem symbolWeight_coordinate (q k : ℕ) (hk : k≤q) (nu : SymbolSpace) (i : Fin 3) :
    |nu i|^k*symbolWeight q nu≤1 := by
  have hr : 1≤1+‖nu‖ := by linarith only [norm_nonneg nu]
  have hi : |nu i|≤1+‖nu‖ := by
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le nu i).trans (by linarith only [norm_nonneg nu])
  have hp : |nu i|^k≤(1+‖nu‖)^q :=
    (pow_le_pow_left₀ (abs_nonneg _) hi k).trans (pow_le_pow_right₀ hr hk)
  unfold symbolWeight
  exact (mul_le_mul_of_nonneg_right hp (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hr) _))).trans_eq
    (mul_inv_cancel₀ (pow_pos (by positivity : (0:ℝ)<1+‖nu‖) q).ne')

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SymbolAverageBound
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The remaining Fourier parameter is averaged against a fixed integrable
weight. A uniform bound survives this averaging with only its fixed mass. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem symbol_average_bound (q : ℕ) (hq : 4≤q) (F : SymbolSpace → ℂ)
    (hF : AEStronglyMeasurable F volume) (C : ℝ)
    (hbound : ∀ᵐ nu ∂volume, ‖F nu‖≤C) :
    Integrable (fun nu => (symbolWeight q nu:ℂ)*F nu) volume ∧
      ‖∫ nu, (symbolWeight q nu:ℂ)*F nu‖≤C*(∫ nu, symbolWeight q nu) := by
  have hw := symbolWeight_integrable q hq
  have hnorm : ∀ᵐ nu ∂volume,
      ‖(symbolWeight q nu:ℂ)*F nu‖ ≤ symbolWeight q nu*C := by
    filter_upwards [hbound] with nu hnu
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (symbolWeight_pos q nu)]
    exact mul_le_mul_of_nonneg_left hnu (symbolWeight_pos q nu).le
  have hi : Integrable (fun nu => (symbolWeight q nu:ℂ)*F nu) volume :=
    (hw.mul_const C).mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable).mul hF) hnorm
  refine ⟨hi,(norm_integral_le_integral_norm _).trans ?_⟩
  calc
    (∫ nu, ‖(symbolWeight q nu:ℂ)*F nu‖)≤∫ nu, symbolWeight q nu*C :=
      integral_mono_ae hi.norm (hw.mul_const C) hnorm
    _ = C*(∫ nu, symbolWeight q nu) := by rw [integral_mul_const]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous packet identity in §2, with the actual convolution
kernels and the exact area normalization. Absolute integrability follows
from L1 kernels and input and a bounded measurable test. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem coefficient_eq (f K : ℝ × ℝ → ℂ) (area : ℝ) (z : ℝ × ℝ) :
    coefficient f area K z = (area : ℂ) * kernelConvolution K f z := by
  unfold coefficient analyzingWave kernelConvolution convolution
  simp only [map_mul, Complex.conj_ofReal, starRingEnd_self_apply, ContinuousLinearMap.mul_apply']
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

theorem kernelConvolution_integrable {K f : ℝ × ℝ → ℂ}
    (hK : Integrable K planeMeasure) (hf : Integrable f planeMeasure) :
    Integrable (kernelConvolution K f) planeMeasure :=
  hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℂ) hK

theorem weighted_convolution_integrable (K c b g : ℝ × ℝ → ℂ)
    (hK : Integrable K planeMeasure) (hc : Integrable c planeMeasure)
    (hb : Measurable b) (hg : Measurable g)
    (Mb Mg : ℝ) (hbb : ∀ x, ‖b x‖≤Mb) (hgb : ∀ x, ‖g x‖≤Mg) :
    Integrable (fun p : (ℝ×ℝ)×(ℝ×ℝ) =>
      (c p.2*K (p.1-p.2))*(b p.1*conj (g p.1))) (planeMeasure.prod planeMeasure) := by
  apply (hc.convolution_integrand (ContinuousLinearMap.mul ℝ ℂ) hK).mul_bdd (c := Mb*Mg)
  · exact ((hb.comp measurable_fst).mul
      (Complex.continuous_conj.measurable.comp (hg.comp measurable_fst))).aestronglyMeasurable
  · filter_upwards [] with p
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hbb p.1) (hgb p.1) (norm_nonneg _) ((norm_nonneg _).trans (hbb p.1))

theorem packetProduct_eq (KA KB f b g : ℝ × ℝ → ℂ) (area : ℝ) (z : ℝ × ℝ) :
    packetProduct KA KB f b g area z = (area : ℂ)^2 * ∫ x,
      (kernelConvolution KB f z*KA (x-z))*(b x*conj (g x)) ∂planeMeasure := by
  rw [packetProduct, coefficient_eq]
  unfold synthesisWave
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem packetProduct_integrable (KA KB f b g : ℝ × ℝ → ℂ)
    (hA : Integrable KA planeMeasure) (hB : Integrable KB planeMeasure)
    (hf : Integrable f planeMeasure) (hb : Measurable b) (hg : Measurable g)
    (Mb Mg : ℝ) (hbb : ∀ x, ‖b x‖≤Mb) (hgb : ∀ x, ‖g x‖≤Mg) (area : ℝ) :
    Integrable (packetProduct KA KB f b g area) planeMeasure := by
  have h := weighted_convolution_integrable KA (kernelConvolution KB f) b g hA
    (kernelConvolution_integrable hB hf) hb hg Mb Mg hbb hgb
  apply (h.integral_prod_right.const_mul ((area:ℂ)^2)).congr
  filter_upwards [] with z
  exact (packetProduct_eq KA KB f b g area z).symm

theorem continuous_packet_identity (KA KB f b g : ℝ × ℝ → ℂ)
    (hA : Integrable KA planeMeasure) (hB : Integrable KB planeMeasure)
    (hf : Integrable f planeMeasure) (hb : Measurable b) (hg : Measurable g)
    (Mb Mg : ℝ) (hbb : ∀ x, ‖b x‖ ≤ Mb) (hgb : ∀ x, ‖g x‖ ≤ Mg)
    (area : ℝ) (ha : area ≠ 0) :
    (∫ x, b x * kernelConvolution KA (kernelConvolution KB f) x * conj (g x) ∂planeMeasure) =
      ((area : ℂ)^2)⁻¹ * ∫ z, coefficient f area KB z *
        (∫ x, b x * synthesisWave area KA z x * conj (g x) ∂planeMeasure) ∂planeMeasure := by
  let c := kernelConvolution KB f
  let H := fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
    (c p.2 * KA (p.1-p.2)) * (b p.1 * conj (g p.1))
  have hc : Integrable c planeMeasure := kernelConvolution_integrable hB hf
  have hH : Integrable H (planeMeasure.prod planeMeasure) :=
    weighted_convolution_integrable KA c b g hA hc hb hg Mb Mg hbb hgb
  have hleft (x : ℝ × ℝ) :
      b x * kernelConvolution KA c x * conj (g x) = ∫ z, H (x,z) ∂planeMeasure := by
    change b x * (∫ z, c z * KA (x-z) ∂planeMeasure) * conj (g x) = _
    rw [← integral_const_mul, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [H]
    ring
  have hright (z : ℝ × ℝ) :
      coefficient f area KB z *
        (∫ x, b x * synthesisWave area KA z x * conj (g x) ∂planeMeasure) =
      (area : ℂ)^2 * ∫ x, H (x,z) ∂planeMeasure := by
    rw [coefficient_eq]
    unfold synthesisWave
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp only [H]
    ring
  have hsum : (∫ z, coefficient f area KB z *
        (∫ x, b x * synthesisWave area KA z x * conj (g x) ∂planeMeasure) ∂planeMeasure) =
      (area : ℂ)^2 * ∫ z, ∫ x, H (x,z) ∂planeMeasure ∂planeMeasure := by
    calc
      _ = ∫ z, (area : ℂ)^2 * ∫ x, H (x,z) ∂planeMeasure ∂planeMeasure :=
        integral_congr_ae (Filter.Eventually.of_forall hright)
      _ = _ := integral_const_mul _ _
  calc
    _ = ∫ x, ∫ z, H (x,z) ∂planeMeasure ∂planeMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall hleft)
    _ = ∫ z, ∫ x, H (x,z) ∂planeMeasure ∂planeMeasure := integral_integral_swap hH
    _ = _ := by
      rw [hsum]
      have ha' : (area : ℂ) ≠ 0 := by exact_mod_cast ha
      field_simp

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlicedIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From almost-everywhere line estimates to planar estimates, including
the area-preserving coordinates of a fixed reference slope. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem integral_slopeShear (s : ℝ) (f : ℝ × ℝ → ℝ) :
    (∫ z, f (slopeShear s z) ∂volume.prod volume) = ∫ z, f z ∂volume.prod volume :=
  (slopeShear_measurePreserving s).integral_comp (slopeShear s).measurableEmbedding f

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PlanarSliceFourierAngular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript uses angular frequencies in `exp(iηy)`, whereas
mathlib's Fourier transform uses `exp(-2πi xξ)`. These definitions and
identities keep the conversion explicit. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

theorem planarAngularFourier_eq_integral (f : ℝ × ℝ → ℂ) (frequency : ℝ × ℝ) :
    planarAngularFourier f frequency = ∫ z : ℝ × ℝ,
      Complex.exp (-(Complex.I * (z.1 * frequency.1 + z.2 * frequency.2))) * f z
        ∂volume.prod volume := by
  unfold planarAngularFourier planarFourier
  simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarSchwartzInversion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier inversion on the actual product plane, and the frozen
multiplier identity for every planar Schwartz input. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert

theorem planarFourier_integrable (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Integrable (planarFourier f) (volume.prod volume) := by
  have h : Integrable (planarFourierSchwartz f : ℝ×ℝ → ℂ) (volume.prod volume) :=
    (planarFourierSchwartz f).integrable
  simpa only [funext (planarFourierSchwartz_apply f)] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShearedLatticePeriodization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact periodization over the translated sheared box lattice used
in the continuous packet representation. -/
noncomputable section
open Set MeasureTheory
open scoped Pointwise ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem latticeHom_injective {l W theta : ℝ} (hl : l ≠ 0) (hW : W ≠ 0) :
    Function.Injective (latticeHom l W theta) := by
  intro n m h
  have h1 : (n.1:ℝ)*l=(m.1:ℝ)*l := congrArg Prod.fst h
  have h2 : theta*(n.1:ℝ)*l+(n.2:ℝ)*W=theta*(m.1:ℝ)*l+(m.2:ℝ)*W :=
    congrArg Prod.snd h
  have hn : n.1=m.1 := by exact_mod_cast (mul_right_cancel₀ hl h1)
  have hk : n.2=m.2 := by
    rw [hn] at h2
    exact_mod_cast (mul_right_cancel₀ hW (add_left_cancel h2))
  exact Prod.ext hn hk

theorem latticeCell_measurable (l W theta : ℝ) : MeasurableSet (latticeCell l W theta) :=
  (measurable_fst measurableSet_Ioc).inter
    ((measurable_snd.sub (measurable_const.mul measurable_fst)) measurableSet_Ioc)

theorem latticeCell_unique {l W theta : ℝ} (hl : 0<l) (hW : 0<W) (x : ℝ × ℝ) :
    ∃! n : ℤ × ℤ, latticeHom l W theta n + x ∈ latticeCell l W theta := by
  obtain ⟨i,hi,hui⟩ := existsUnique_add_zsmul_mem_Ioc hl x.1 0
  obtain ⟨j,hj,huj⟩ := existsUnique_add_zsmul_mem_Ioc hW (x.2-theta*x.1) 0
  have hcoord (n : ℤ × ℤ) :
      (latticeHom l W theta n+x).2-theta*(latticeHom l W theta n+x).1 =
        x.2-theta*x.1+(n.2:ℝ)*W := by
    simp only [latticeHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.fst_add, Prod.snd_add]
    ring
  have hmem (n : ℤ × ℤ) : latticeHom l W theta n+x ∈ latticeCell l W theta ↔
      x.1+n.1 • l ∈ Ioc 0 (0+l) ∧ (x.2-theta*x.1)+n.2 • W ∈ Ioc 0 (0+W) := by
    change (_ ∈ Ioc 0 l ∧ _ ∈ Ioc 0 W) ↔ _
    rw [hcoord]
    simp only [latticeHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.fst_add, zero_add,
      zsmul_eq_mul, add_comm ((n.1:ℝ)*l)]
  refine ⟨(i,j), (hmem _).2 ⟨hi,hj⟩, ?_⟩
  intro n hn
  exact Prod.ext (hui _ ((hmem n).1 hn).1) (huj _ ((hmem n).1 hn).2)

theorem latticeCell_fundamental {l W theta : ℝ} (hl : 0<l) (hW : 0<W) :
    IsAddFundamentalDomain (latticeHom l W theta).range (latticeCell l W theta) planeMeasure := by
  let e := AddMonoidHom.ofInjective (latticeHom_injective (theta := theta) hl.ne' hW.ne')
  apply IsAddFundamentalDomain.mk' (latticeCell_measurable l W theta).nullMeasurableSet
  intro x
  obtain ⟨n,hn,hun⟩ := latticeCell_unique (theta := theta) hl hW x
  refine ⟨e n,hn,?_⟩
  intro g hg
  change (g : ℝ × ℝ)+x ∈ latticeCell l W theta at hg
  have hs : e.symm g=n := hun (e.symm g) (by
    change (e (e.symm g) : ℝ × ℝ)+x ∈ latticeCell l W theta
    simpa only [e.apply_symm_apply] using hg)
  calc
    g = e (e.symm g) := (e.apply_symm_apply g).symm
    _ = e n := congrArg e hs

theorem sheared_lattice_periodization {l W theta : ℝ} (hl : 0<l) (hW : 0<W)
    (F : ℝ × ℝ → ℂ) (hF : Integrable F planeMeasure) :
    (∫ x, F x ∂planeMeasure) =
      ∫ z in latticeCell l W theta, ∑' n : ℤ × ℤ, F (latticeHom l W theta n+z) ∂planeMeasure := by
  let G := (latticeHom l W theta).range
  let e : (ℤ × ℤ) ≃+ G :=
    AddMonoidHom.ofInjective (latticeHom_injective (theta := theta) hl.ne' hW.ne')
  let : Countable G := Countable.of_equiv (ℤ × ℤ) e.toEquiv
  have hs := latticeCell_fundamental (theta := theta) hl hW
  have hm (g : G) : AEStronglyMeasurable (fun z => F (g+ᵥz))
      (planeMeasure.restrict (latticeCell l W theta)) :=
    (hF.aestronglyMeasurable.comp_measurePreserving (measurePreserving_add_left planeMeasure (g:ℝ×ℝ))).restrict
  have hsum : (∑' g : G, ∫⁻ z in latticeCell l W theta, ‖F (g+ᵥz)‖ₑ ∂planeMeasure) ≠ ∞ := by
    rw [← hs.lintegral_eq_tsum'' (fun z => ‖F z‖ₑ)]
    exact hF.hasFiniteIntegral.ne
  calc
    _ = ∑' g : G, ∫ z in latticeCell l W theta, F (g+ᵥz) ∂planeMeasure :=
      hs.integral_eq_tsum'' F hF
    _ = ∫ z in latticeCell l W theta, ∑' g : G, F (g+ᵥz) ∂planeMeasure :=
      (integral_tsum hm hsum).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact (e.toEquiv.tsum_eq (fun g : G => F (g+ᵥz))).symm


theorem latticeCell_volume {l W theta : ℝ} (hl : 0<l) (_hW : 0<W) :
    planeMeasure (latticeCell l W theta) = ENNReal.ofReal (l*W) := by
  have heq : latticeCell l W theta =
      (slopeShear (-theta)) ⁻¹' ((Ioc 0 l) ×ˢ (Ioc 0 W)) := by
    ext x
    change (x.1 ∈ Ioc 0 l ∧ x.2-theta*x.1 ∈ Ioc 0 W) ↔
      (x.1 ∈ Ioc 0 l ∧ x.2+(-theta)*x.1 ∈ Ioc 0 W)
    simp only [neg_mul, sub_eq_add_neg]
  rw [heq, (slopeShear_measurePreserving (-theta)).measure_preimage_equiv,
    Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc, sub_zero, sub_zero,
    ← ENNReal.ofReal_mul hl.le]

theorem latticeAverage_probability {l W theta : ℝ} (hl : 0<l) (hW : 0<W) :
    IsProbabilityMeasure (latticeAverage l W theta) where
  measure_univ := by
    rw [latticeAverage, Measure.smul_apply, Measure.restrict_apply_univ, latticeCell_volume hl hW,
      smul_eq_mul, ENNReal.inv_mul_cancel]
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos hl hW))
    · exact ENNReal.ofReal_ne_top

theorem integral_latticeAverage {l W theta : ℝ} (hl : 0<l) (hW : 0<W)
    (F : ℝ × ℝ → ℂ) :
    (∫ z, F z ∂latticeAverage l W theta) =
      ((l*W)⁻¹ : ℝ) • ∫ z in latticeCell l W theta, F z ∂planeMeasure := by
  rw [latticeAverage, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (mul_pos hl hW).le]

theorem sheared_lattice_summable {l W theta : ℝ} (hl : 0<l) (hW : 0<W)
    (F : ℝ × ℝ → ℂ) (hF : Integrable F planeMeasure) :
    ∀ᵐ z ∂latticeAverage l W theta,
      Summable (fun n : ℤ×ℤ => ‖F (latticeHom l W theta n+z)‖) := by
  let G := (latticeHom l W theta).range
  let e : (ℤ×ℤ) ≃+ G :=
    AddMonoidHom.ofInjective (latticeHom_injective (theta := theta) hl.ne' hW.ne')
  let : Countable G := Countable.of_equiv (ℤ×ℤ) e.toEquiv
  have hs := latticeCell_fundamental (theta := theta) hl hW
  have hm (g : G) : AEMeasurable (fun z => ‖F (g+ᵥz)‖ₑ)
      (planeMeasure.restrict (latticeCell l W theta)) :=
    ((hF.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_add_left planeMeasure (g:ℝ×ℝ))).restrict).enorm
  have hi : (∫⁻ z in latticeCell l W theta, ∑' g : G, ‖F (g+ᵥz)‖ₑ ∂planeMeasure) ≠ ∞ := by
    rw [lintegral_tsum hm, ← hs.lintegral_eq_tsum'' (fun z => ‖F z‖ₑ)]
    exact hF.hasFiniteIntegral.ne
  have ha := ae_lt_top' (AEMeasurable.tsum hm) hi
  apply Measure.ae_smul_measure _ ((ENNReal.ofReal (l*W))⁻¹)
  filter_upwards [ha] with z hz
  apply tsum_enorm_ne_top_iff_summable_norm.mp
  have he : (∑' n : ℤ×ℤ, ‖F (latticeHom l W theta n+z)‖ₑ) =
      ∑' g : G, ‖F (g+ᵥz)‖ₑ := e.toEquiv.tsum_eq (fun g : G => ‖F (g+ᵥz)‖ₑ)
  rw [he]
  exact hz.ne

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_FactoredMultiplierPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A factored frequency multiplier is exactly the normalized average
of its actual analyzing and synthesizing convolution packets. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
namespace LipschitzHilbert

theorem planarSchwartzConvolution_apply (K f : SchwartzMap (ℝ×ℝ) ℂ) (x : ℝ×ℝ) :
    planarSchwartzConvolution K f x=PacketRepresentation.kernelConvolution K f x := by
  change SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
    (hilbertPlanarSchwartz f) (hilbertPlanarSchwartz K) (WithLp.toLp 2 x)=_
  rw [SchwartzMap.convolution_apply, MeasureTheory.convolution, integral_hilbertPlanar_bridge]
  rfl

theorem planarFourier_convolution (K f : SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ) :
    planarFourier (planarSchwartzConvolution K f) omega=
      planarFourier K omega*planarFourier f omega := by
  rw [← fourier_hilbertPlanar_bridge, planarSchwartzConvolution, hilbertPlanar_lower,
    SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
    fourier_hilbertPlanar_bridge, fourier_hilbertPlanar_bridge]
  exact mul_comm _ _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_L1FourierConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier multiplication by a Schwartz kernel is convolution for every
L1 input. This includes the measurable amplitude slices used after binning. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem planarFourier_l1_bound (f : ℝ×ℝ → ℂ) (omega : ℝ×ℝ) :
    ‖planarFourier f omega‖≤∫ z, ‖f z‖ ∂planeMeasure := by
  unfold planarFourier
  simpa only [Circle.norm_smul] using
    norm_integral_le_integral_norm (fun z : ℝ×ℝ =>
      Real.fourierChar (-(z.1*omega.1+z.2*omega.2)) • f z)

theorem planarFourier_l1_continuous (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) :
    Continuous (planarFourier f) := by
  unfold planarFourier
  apply continuous_of_dominated (bound:=fun z => ‖f z‖)
  · intro omega
    exact ((show Continuous (fun z : ℝ×ℝ =>
      Real.fourierChar (-(z.1*omega.1+z.2*omega.2))) by fun_prop).aestronglyMeasurable.smul
      hf.aestronglyMeasurable)
  · intro omega
    exact Filter.Eventually.of_forall (fun z => le_of_eq (Circle.norm_smul _ _))
  · exact hf.norm
  · exact Filter.Eventually.of_forall (fun z => by fun_prop)

theorem planarInverse_mul_fourier_l1 (K : SchwartzMap (ℝ×ℝ) ℂ)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) (x : ℝ×ℝ) :
    planarInverse (fun omega => planarFourier K omega*planarFourier f omega) x=
      kernelConvolution K f x := by
  let H := fun p : (ℝ×ℝ)×(ℝ×ℝ) =>
    (planarFourier K p.1*f p.2)*
      (Real.fourierChar ((x.1-p.2.1)*p.1.1+(x.2-p.2.2)*p.1.2):ℂ)
  have hH : Integrable H (planeMeasure.prod planeMeasure) := by
    apply ((planarFourier_integrable K).mul_prod hf).mul_bdd (c:=1)
    · exact (show Continuous (fun p : (ℝ×ℝ)×(ℝ×ℝ) =>
        (Real.fourierChar ((x.1-p.2.1)*p.1.1+(x.2-p.2.2)*p.1.2):ℂ)) by fun_prop).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun p => le_of_eq (Circle.norm_coe _))
  have hleft (omega : ℝ×ℝ) :
      Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (planarFourier K omega*planarFourier f omega)=∫ y, H (omega,y) ∂planeMeasure := by
    change Real.fourierChar (x.1*omega.1+x.2*omega.2) •
      (planarFourier K omega*(∫ y, Real.fourierChar (-(y.1*omega.1+y.2*omega.2)) • f y ∂planeMeasure))=_
    simp only [Circle.smul_def,smul_eq_mul]
    rw [←integral_const_mul,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [H]
    have hphase : (x.1-y.1)*omega.1+(x.2-y.2)*omega.2=
        (x.1*omega.1+x.2*omega.2)+(-(y.1*omega.1+y.2*omega.2)) := by ring
    rw [hphase]
    simp only [Real.fourierChar.map_add_eq_mul]
    push_cast
    ring
  have hright (y : ℝ×ℝ) : (∫ omega, H (omega,y) ∂planeMeasure)=K (x-y)*f y := by
    have hinv := planarFourier_inversion K (x-y)
    change (∫ omega, (planarFourier K omega*f y)*
      (Real.fourierChar ((x.1-y.1)*omega.1+(x.2-y.2)*omega.2):ℂ) ∂planeMeasure)=_
    calc
      _ = (∫ omega, Real.fourierChar ((x.1-y.1)*omega.1+(x.2-y.2)*omega.2) •
          planarFourier K omega ∂planeMeasure)*f y := by
        rw [←integral_mul_const]
        apply integral_congr_ae
        filter_upwards [] with omega
        simp only [Circle.smul_def,smul_eq_mul]
        ring
      _ = _ := by
        change planarInverse (planarFourier K) (x-y)*f y=K (x-y)*f y
        rw [hinv]
  calc
    _ = ∫ omega, ∫ y, H (omega,y) ∂planeMeasure ∂planeMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall hleft)
    _ = ∫ y, ∫ omega, H (omega,y) ∂planeMeasure ∂planeMeasure := integral_integral_swap hH
    _ = ∫ y, K (x-y)*f y ∂planeMeasure := integral_congr_ae (Filter.Eventually.of_forall hright)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact mul_comm _ _

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_L1FactoredConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two Schwartz frequency factors retain their exact convolution
representation on every L1 amplitude slice. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem kernelConvolution_schwartz_assoc_l1 (KA KB : SchwartzMap (ℝ×ℝ) ℂ)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) (x : ℝ×ℝ) :
    kernelConvolution (planarSchwartzConvolution KA KB) f x=
      kernelConvolution KA (kernelConvolution KB f) x := by
  let L := ContinuousLinearMap.mul ℝ ℂ
  have hKA : Integrable KA planeMeasure := KA.integrable
  have hKB : Integrable KB planeMeasure := KB.integrable
  have hfg := hf.ae_convolution_exists L hKB
  have hgk := hKB.ae_convolution_exists L hKA
  have hi : Integrable (fun p : (ℝ×ℝ)×(ℝ×ℝ) =>
      (f p.2*KB (p.1-p.2))*KA (x-p.1)) (planeMeasure.prod planeMeasure) := by
    apply (hf.convolution_integrand L hKB).mul_bdd (c:=SchwartzMap.seminorm ℝ 0 0 KA)
    · exact (KA.continuous.comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun p => SchwartzMap.norm_le_seminorm ℝ KA _)
  have h := convolution_assoc' (x₀:=x) L L L L (fun a b c => mul_assoc a b c) hfg hgk
    (by
      apply hi.congr
      filter_upwards [] with p
      change (f p.2*KB (p.1-p.2))*KA (x-p.1)=f p.2*(KB (p.1-p.2)*KA (x-p.1))
      ring)
  have heq : (planarSchwartzConvolution KA KB : ℝ×ℝ → ℂ)=kernelConvolution KA KB :=
    funext (planarSchwartzConvolution_apply KA KB)
  rw [heq]
  exact h.symm

theorem factored_multiplier_convolution_l1 (KA KB : SchwartzMap (ℝ×ℝ) ℂ)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) (x : ℝ×ℝ) :
    planarInverse (fun omega => planarFourier KA omega*planarFourier KB omega*planarFourier f omega) x=
      kernelConvolution KA (kernelConvolution KB f) x := by
  have heq : (fun omega => planarFourier KA omega*planarFourier KB omega*planarFourier f omega)=
      (fun omega => planarFourier (planarSchwartzConvolution KA KB) omega*planarFourier f omega) := by
    funext omega
    rw [planarFourier_convolution]
  rw [heq,planarInverse_mul_fourier_l1 _ f hf,kernelConvolution_schwartz_assoc_l1 KA KB f hf]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_ConvolutionPacketSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translation, reflection, and conjugation for the actual convolution
packets. The analyzing packet retains the original positive-frequency
support; reflection and conjugation cancel their frequency reversals. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem synthesisWave_fourier (area : ℝ) (K : ℝ×ℝ → ℂ) (z : ℝ×ℝ) (xi eta : ℝ) :
    planarAngularFourier (synthesisWave area K z) (xi,eta)=
      (area:ℂ)*Complex.exp (-(Complex.I*((z.1:ℂ)*xi+(z.2:ℂ)*eta)))*
        planarAngularFourier K (xi,eta) := by
  rw [planarAngularFourier_eq_integral, planarAngularFourier_eq_integral]
  let H := fun y : ℝ×ℝ => Complex.exp (-(Complex.I*((y.1:ℂ)*xi+(y.2:ℂ)*eta)))*
    synthesisWave area K z y
  have ht := integral_add_right_eq_self (μ := planeMeasure) H z
  change (∫ y, H y ∂planeMeasure)=_
  rw [← ht, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  dsimp [H,synthesisWave]
  simp only [add_sub_cancel_right, Complex.ofReal_add]
  rw [show -(Complex.I*(((y.1:ℂ)+(z.1:ℂ))*xi+((y.2:ℂ)+(z.2:ℂ))*eta))=
      -(Complex.I*((z.1:ℂ)*xi+(z.2:ℂ)*eta))+
        -(Complex.I*((y.1:ℂ)*xi+(y.2:ℂ)*eta)) by ring, Complex.exp_add]
  ring

theorem analyzingWave_fourier (area : ℝ) (K : ℝ×ℝ → ℂ) (z : ℝ×ℝ) (xi eta : ℝ) :
    planarAngularFourier (analyzingWave area K z) (xi,eta)=
      (area:ℂ)*Complex.exp (-(Complex.I*((z.1:ℂ)*xi+(z.2:ℂ)*eta)))*
        conj (planarAngularFourier K (xi,eta)) := by
  rw [planarAngularFourier_eq_integral, planarAngularFourier_eq_integral]
  let H := fun y : ℝ×ℝ => Complex.exp (-(Complex.I*((y.1:ℂ)*xi+(y.2:ℂ)*eta)))*
    analyzingWave area K z y
  have ht := integral_sub_left_eq_self (μ := planeMeasure) H z
  change (∫ y, H y ∂planeMeasure)=_
  rw [← ht, ← integral_conj, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  dsimp [H,analyzingWave]
  simp only [sub_sub_cancel, Complex.ofReal_sub, map_mul]
  rw [← Complex.exp_conj]
  simp only [map_neg, map_mul, map_add, Complex.conj_I, Complex.conj_ofReal]
  rw [show -(Complex.I*(((z.1:ℂ)-(y.1:ℂ))*xi+((z.2:ℂ)-(y.2:ℂ))*eta))=
      -(Complex.I*((z.1:ℂ)*xi+(z.2:ℂ)*eta))+
        -((-Complex.I)*((y.1:ℂ)*xi+(y.2:ℂ)*eta)) by ring, Complex.exp_add]
  ring

theorem synthesisWave_spectrum {S : Set (ℝ×ℝ)} (area : ℝ) (K : ℝ×ℝ → ℂ)
    (hK : ∀ omega, planarAngularFourier K omega≠0 → omega∈S)
    (z : ℝ×ℝ) (omega : ℝ×ℝ)
    (h : planarAngularFourier (synthesisWave area K z) omega≠0) : omega∈S := by
  apply hK omega
  intro hz
  rcases omega with ⟨xi,eta⟩
  rw [synthesisWave_fourier, hz, mul_zero] at h
  exact h rfl

theorem analyzingWave_spectrum {S : Set (ℝ×ℝ)} (area : ℝ) (K : ℝ×ℝ → ℂ)
    (hK : ∀ omega, planarAngularFourier K omega≠0 → omega∈S)
    (z : ℝ×ℝ) (omega : ℝ×ℝ)
    (h : planarAngularFourier (analyzingWave area K z) omega≠0) : omega∈S := by
  apply hK omega
  intro hz
  rcases omega with ⟨xi,eta⟩
  rw [analyzingWave_fourier, hz, map_zero, mul_zero] at h
  exact h rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual decaying top weights and their motion along a reference line. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace SlopeBox

theorem radius_nonnegative (T : SlopeBox) (z : ℝ × ℝ) : 0 ≤ T.radius z :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceThreeGridCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal three-grid covering lemma for the nested alternating
one-third grids. It supplies the interval comparison in the maximal
kernel estimate. -/
noncomputable section
open Set
namespace LipschitzHilbert.DyadicLineGrid

theorem shift_signed_third (k : ℤ) : shift (k.negOnePow:ℤ) k=1/3 := by
  simp only [shift,←Units.val_mul,Int.units_mul_self,Units.val_one,Int.cast_one]

theorem signed_third_in_range (k : ℤ) : (k.negOnePow:ℤ)∈Finset.Icc (-1) 1 := by
  rw [Finset.mem_Icc]
  exact abs_le.mp (le_of_eq (Int.abs_negOnePow k))

/-- A closed interval of radius less than one sixth of a grid cell
fits in a cell of one of the three fixed nested grids. -/
theorem exists_three_grid_cover (k : ℤ) (c r : ℝ) (_hr : 0 ≤ r)
    (hsmall : 6*r < scale k) :
    ∃ q∈Finset.Icc (-1) 1, ∃ j : ℤ, Icc (c-r) (c+r)⊆cell q k j := by
  let m := index 0 k c
  let a := left 0 k m
  have hc := mem_index_cell 0 k c
  have hright : left 0 k (m+1)=a+scale k := by
    dsimp [a,left,shift]
    push_cast
    ring
  change a ≤ c ∧ c<left 0 k (m+1) at hc
  rw [hright] at hc
  by_cases hleft : a ≤ c-r
  · by_cases hend : c+r<a+scale k
    · refine ⟨0,by simp, m,?_⟩
      intro x hx
      exact ⟨hleft.trans hx.1,hx.2.trans_lt (by simpa only [hright] using hend)⟩
    · refine ⟨(k.negOnePow:ℤ),signed_third_in_range k,m,?_⟩
      intro x hx
      change left (k.negOnePow:ℤ) k m≤x ∧ x<left (k.negOnePow:ℤ) k (m+1)
      have hl : left (k.negOnePow:ℤ) k m=a+scale k/3 := by
        simp only [left,shift_signed_third]
        dsimp [a,left,shift]
        push_cast
        ring
      have hu : left (k.negOnePow:ℤ) k (m+1)=a+4*scale k/3 := by
        simp only [left,shift_signed_third]
        dsimp [a,left,shift]
        push_cast
        ring
      rw [hl,hu]
      constructor <;> linarith [hx.1,hx.2]
  · refine ⟨(k.negOnePow:ℤ),signed_third_in_range k,m-1,?_⟩
    intro x hx
    change left (k.negOnePow:ℤ) k (m-1)≤x ∧
      x<left (k.negOnePow:ℤ) k (m-1+1)
    have hl : left (k.negOnePow:ℤ) k (m-1)=a-2*scale k/3 := by
      simp only [left,shift_signed_third]
      dsimp [a,left,shift]
      push_cast
      ring
    have hu : left (k.negOnePow:ℤ) k (m-1+1)=a+scale k/3 := by
      simp only [left,shift_signed_third]
      dsimp [a,left,shift]
      push_cast
      ring
    rw [hl,hu]
    constructor <;> linarith [hx.1,hx.2]

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceThreeGridMaximal
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual interval maximal majorant built from three nested grids.
The exceptional set is independent of the real interval parameters. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.DyadicLineGrid

theorem gridChoice_card : Fintype.card GridChoice=3 := by
  simp [GridChoice]

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceVerticalDemodulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing each vertical bin carrier is an exact pointwise isometry.
Box reproduction can therefore use the narrow demodulated spectra. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert
open DyadicLineGrid
variable {κ : Type*} [Fintype κ]

theorem verticalCarrier_temperate (nu : ℝ) : Function.HasTemperateGrowth (verticalCarrier nu) := by
  change Function.HasTemperateGrowth (fun z : ℝ×ℝ => Complex.exp ((nu*z.2 : ℝ)*Complex.I))
  simpa only [sub_zero,zero_mul] using physicalPacketCarrier_temperate 0 0 0 nu

@[simp] theorem verticalDemodulation_apply (nu : κ → ℝ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (z : ℝ×ℝ) (k : κ) :
    verticalDemodulation nu f z k=verticalCarrier (-nu k) z*f z k := by
  rw [verticalDemodulation,vectorSchwartz_apply,
    SchwartzMap.smulLeftCLM_apply_apply (verticalCarrier_temperate (-nu k))]
  rfl

@[simp] theorem verticalDemodulation_norm (nu : κ → ℝ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (z : ℝ×ℝ) :
    ‖verticalDemodulation nu f z‖=‖f z‖ := by
  have h : ‖verticalDemodulation nu f z‖^2=‖f z‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq,verticalDemodulation_apply,norm_mul,
      verticalCarrier_norm,one_mul]
  nlinarith [norm_nonneg (verticalDemodulation nu f z),norm_nonneg (f z)]

@[simp] theorem scalarVerticalDemodulation_apply (nu : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    scalarVerticalDemodulation nu f z=verticalCarrier (-nu) z*f z := by
  exact SchwartzMap.smulLeftCLM_apply_apply (verticalCarrier_temperate (-nu)) f z

@[simp] theorem verticalDemodulation_zero (nu : κ → ℝ) :
    verticalDemodulation nu 0=0 := by
  ext z k
  simp

@[simp] theorem verticalDemodulation_sub (nu : κ → ℝ)
    (f g : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) :
    verticalDemodulation nu (f-g)=verticalDemodulation nu f-verticalDemodulation nu g := by
  ext z k
  simp [mul_sub]

@[simp] theorem verticalDemodulation_sum {J : Type*} (nu : κ → ℝ) (s : Finset J)
    (f : J → SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) :
    verticalDemodulation nu (∑ j∈s, f j)=∑ j∈s, verticalDemodulation nu (f j) := by
  ext z k
  simp [sum_apply,WithLp.ofLp_sum,Finset.sum_apply,Finset.mul_sum]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_ConvolutionPacketProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized Schwartz profiles for the actual convolution packets,
with arbitrary prescribed vertical carrier. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem convolutionProfile_apply (K : SchwartzMap (ℝ×ℝ) ℂ) (l W theta nu : ℝ)
    (hl : l≠0) (hW : W≠0) (q : ℝ×ℝ) :
    convolutionProfile K l W theta nu hl hW q =
      (l*W:ℂ)*Complex.exp ((-(nu*W)*q.2:ℝ)*Complex.I)*
        K ((packetCoordinates l W theta hl hW).symm q) := by
  rw [convolutionProfile, smul_apply, scalarVerticalDemodulation_apply]
  simp only [verticalCarrier, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, smul_eq_mul]
  ring

theorem physical_convolution_packet (K : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta nu : ℝ) (hl : l≠0) (hW : W≠0) (z x : ℝ×ℝ) :
    physicalPlanarPacket (convolutionProfile K l W theta nu hl hW)
      z.1 z.2 l W theta nu hl hW x=synthesisWave (l*W) K z x := by
  rw [physicalPlanarPacket_apply, convolutionProfile_apply]
  have harg : (packetCoordinates l W theta hl hW).symm
      ((x.1-z.1)/l,((x.2-z.2)-theta*(x.1-z.1))/W)=x-z :=
    (packetCoordinates l W theta hl hW).symm_apply_apply (x-z)
  rw [harg]
  have hp : ((nu*((x.2-z.2)-theta*(x.1-z.1)):ℝ):ℂ)*Complex.I+
      ((-(nu*W)*(((x.2-z.2)-theta*(x.1-z.1))/W):ℝ):ℂ)*Complex.I=0 := by
    push_cast
    field_simp [show (W:ℂ)≠0 by exact_mod_cast hW]
    ring
  calc
    _ = (Complex.exp (((nu*((x.2-z.2)-theta*(x.1-z.1)):ℝ):ℂ)*Complex.I)*
        Complex.exp (((-(nu*W)*(((x.2-z.2)-theta*(x.1-z.1))/W):ℝ):ℂ)*Complex.I))*
          ((l*W:ℂ)*K (x-z)) := by ring
    _ = _ := by
      rw [← Complex.exp_add, hp, Complex.exp_zero, one_mul]
      simp only [synthesisWave, Complex.ofReal_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedBandSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized coordinates and support geometry in the packet
representation of the annular band multiplier (§2). -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

/-- The wave slopes stay in a fixed multiple of the angular scale
around the lattice label. -/
theorem frequency_slope_margin (l w xi eta theta c C : ℝ)
    (hl : 0<l) (hw : 0<w) (hc : 0 < c) (hC : 0≤C)
    (hV : c≤w*eta) (hX : |symbolX l xi eta theta|≤C) :
    |(-xi/eta)-theta|≤(C/c)*(w/l) := by
  have heta : 0<eta := pos_of_mul_pos_right (hc.trans_le hV) hw.le
  have hscale : |(-xi/eta)-theta|=|symbolX l xi eta theta|/(l*eta) := by
    unfold symbolX
    rw [abs_mul, abs_of_pos hl]
    have hid : -xi/eta-theta=-(xi+theta*eta)/eta := by field_simp; ring
    rw [hid, abs_div, abs_neg, abs_of_pos heta]
    field_simp
  rw [hscale]
  apply (div_le_iff₀ (mul_pos hl heta)).2
  calc
    _ ≤ C := hX
    _ ≤ (C/c)*(w/l)*(l*eta) := by
      have hb : C≤(C/c)*(w*eta) := by
        calc
          C = (C/c)*c := by field_simp
          _ ≤ (C/c)*(w*eta) := mul_le_mul_of_nonneg_left hV (div_nonneg hC hc.le)
      convert hb using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularSelector
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed smooth annular selector. Multiplying the separated selector
by this cutoff gives the required support away from the reference slope. -/
noncomputable section
open scoped ContDiff FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem annularCutoff_apply (a b : ℝ) (ha : 0<a) (hb : 0<b) (U : ℝ) :
    annularCutoff a b ha hb U=selectorOuter b hb U*(1-selectorInner a ha U) := rfl

theorem annularCutoff_nonneg (a b : ℝ) (ha : 0<a) (hb : 0<b) (U : ℝ) :
    0≤annularCutoff a b ha hb U :=
  mul_nonneg (selectorOuter b hb).nonneg (sub_nonneg.mpr (selectorInner a ha).le_one)

theorem annularCutoff_le_one (a b : ℝ) (ha : 0<a) (hb : 0<b) (U : ℝ) :
    annularCutoff a b ha hb U≤1 := by
  have hi := (selectorInner a ha).nonneg (x := U)
  have ho := (selectorOuter b hb).le_one (x := U)
  calc
    _ ≤ selectorOuter b hb U*1 :=
      mul_le_mul_of_nonneg_left (by linarith only [hi]) (selectorOuter b hb).nonneg
    _ ≤ 1 := by simpa only [mul_one] using ho

theorem annularCutoff_support (a b : ℝ) (ha : 0<a) (hb : 0<b) (U : ℝ)
    (h : annularCutoff a b ha hb U≠0) : a/2 < |U| ∧ |U|<2*b := by
  constructor
  · by_contra hn
    have hi : selectorInner a ha U=1 :=
      (selectorInner a ha).one_of_mem_closedBall
        (by simpa [selectorInner, Real.dist_eq] using le_of_not_gt hn)
    apply h
    rw [annularCutoff_apply, hi, sub_self, mul_zero]
  · by_contra hn
    have ho : selectorOuter b hb U=0 :=
      (selectorOuter b hb).zero_of_le_dist
        (by simpa [selectorOuter, Real.dist_eq] using le_of_not_gt hn)
    apply h
    rw [annularCutoff_apply, ho, zero_mul]

theorem localizedSelector_bound (chi : SchwartzMap ℝ ℝ) (hchi : ∀ U, |chi U|≤1)
    (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (nu : SymbolSpace) (U : ℝ) :
    ‖localizedSelector chi S q nu U‖ ≤ symbolCoefficientBound S q*symbolWeight q nu := by
  rw [localizedSelector, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (hchi U) (norm_nonneg _)).trans
    (by simpa only [one_mul] using weightedSelector_bound S q nu U)

theorem localizedSelector_support (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (nu : SymbolSpace) (U : ℝ)
    (h : localizedSelector (annularCutoff a b ha hb) S q nu U≠0) : a/2 < |U| ∧ |U|<2*b := by
  apply annularCutoff_support a b ha hb U
  intro hz
  apply h
  simp only [localizedSelector, hz, Complex.ofReal_zero, zero_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SeparatedSymbolOperator
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini separates the normalized symbol inside the actual planar
frequency integral. The direction parameter is frozen only at its output. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem separated_symbol_operator (S : SchwartzMap SymbolSpace ℂ)
    (F : ℝ×ℝ → ℂ) (hF : Integrable F planeMeasure)
    (l W theta center U : ℝ) (x : ℝ×ℝ) :
    (∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
      (S (symbolPoint (symbolX l omega.1 omega.2 theta) (symbolY W omega.2 center) U)*F omega)
        ∂planeMeasure) =
      ∫ nu : SymbolSpace, (𝓕 S nu*selectorCharacter nu U)*
        planarInverse (modulatedFrequency F nu l W theta center) x := by
  let phase := fun (nu : SymbolSpace) (omega : ℝ×ℝ) =>
    frequencyCharacter nu (symbolX l omega.1 omega.2 theta) (symbolY W omega.2 center)*
      selectorCharacter nu U*(Real.fourierChar (x.1*omega.1+x.2*omega.2):ℂ)
  let H := fun p : SymbolSpace×(ℝ×ℝ) => (𝓕 S p.1*F p.2)*phase p.1 p.2
  have hH : Integrable H (volume.prod planeMeasure) := by
    apply ((𝓕 S : SchwartzMap SymbolSpace ℂ).integrable.mul_prod hF).mul_bdd (c := 1)
    · exact (show Continuous (fun p : SymbolSpace×(ℝ×ℝ) => phase p.1 p.2) by
        unfold phase frequencyCharacter selectorCharacter symbolX symbolY; fun_prop).aestronglyMeasurable
    · filter_upwards [] with p
      dsimp only [phase]
      rw [norm_mul, norm_mul, norm_frequencyCharacter, norm_selectorCharacter, Circle.norm_coe]
      norm_num
  have hleft (omega : ℝ×ℝ) :
      Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (S (symbolPoint (symbolX l omega.1 omega.2 theta) (symbolY W omega.2 center) U)*F omega)=
          ∫ nu : SymbolSpace, H (nu,omega) := by
    rw [separated_symbol_fourier]
    simp only [Circle.smul_def, smul_eq_mul]
    rw [← integral_mul_const, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with nu
    dsimp only [H,phase]
    ring
  have hright (nu : SymbolSpace) : (∫ omega, H (nu,omega) ∂planeMeasure)=
      (𝓕 S nu*selectorCharacter nu U)*
        planarInverse (modulatedFrequency F nu l W theta center) x := by
    rw [planarInverse, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with omega
    simp only [H,phase,modulatedFrequency,Circle.smul_def,smul_eq_mul]
    ring
  calc
    _ = ∫ omega, (∫ nu : SymbolSpace, H (nu,omega)) ∂planeMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall hleft)
    _ = ∫ nu : SymbolSpace, ∫ omega, H (nu,omega) ∂planeMeasure :=
      (integral_integral_swap hH).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hright)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LocalizedSymbolOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The localized symbol is a weighted average of genuine planar
frequency multipliers, with two powers of the weight assigned to the waves. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem planarInverse_const_mul (c : ℂ) (F : ℝ×ℝ → ℂ) (x : ℝ×ℝ) :
    planarInverse (fun omega => c*F omega) x=c*planarInverse F x := by
  simp only [planarInverse, Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with omega
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarFrequencyPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two separated frequency factors are Fourier transforms of actual
Schwartz convolution kernels. Thus the lattice average uses actual packets. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem planarInverseSchwartz_apply (F : SchwartzMap (ℝ×ℝ) ℂ) (x : ℝ×ℝ) :
    planarInverseSchwartz F x=planarInverse F x := by
  rw [← planarFourier_inversion (planarInverseSchwartz F) x]
  congr 1
  funext omega
  exact planarInverseSchwartz_fourier F omega

theorem affineFrequencyCharacter_temperate (a b c : ℝ) :
    Function.HasTemperateGrowth (fun omega : ℝ×ℝ =>
      (Real.fourierChar (a*omega.1+b*omega.2+c):ℂ)) := by
  have hx : Function.HasTemperateGrowth (fun omega : ℝ×ℝ => omega.1) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasTemperateGrowth
  have hy : Function.HasTemperateGrowth (fun omega : ℝ×ℝ => omega.2) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasTemperateGrowth
  exact Function.HasTemperateGrowth.comp (g := fun t : ℝ => Complex.exp (t * Complex.I)) OAI.hasTemperateGrowth_exp_mul_I (by fun_prop)

theorem modulatedFrequencyWindow_apply (F : SchwartzMap (ℝ×ℝ) ℂ)
    (a b c : ℝ) (omega : ℝ×ℝ) :
    modulatedFrequencyWindow F a b c omega=
      (Real.fourierChar (a*omega.1+b*omega.2+c):ℂ)*F omega :=
  SchwartzMap.smulLeftCLM_apply_apply (affineFrequencyCharacter_temperate a b c) F omega

theorem frequencyKernel_product (A B : SchwartzMap (ℝ×ℝ) ℂ) (nu : SymbolSpace)
    (q : ℕ) (l W theta center : ℝ) (omega : ℝ×ℝ) :
    planarFourier (horizontalFrequencyKernel A nu q l theta) omega*
      planarFourier (verticalFrequencyKernel B nu q W center) omega=
        (symbolWeight q nu:ℂ)^2*
          modulatedFrequency (fun omega => A omega*B omega) nu l W theta center omega := by
  rw [horizontalFrequencyKernel, verticalFrequencyKernel,
    planarInverseSchwartz_fourier, planarInverseSchwartz_fourier]
  simp only [smul_apply, smul_eq_mul, modulatedFrequencyWindow_apply,
    modulatedFrequency, frequencyCharacter]
  have hx : nu 0*l*omega.1+nu 0*l*theta*omega.2+0=
      nu 0*symbolX l omega.1 omega.2 theta := by unfold symbolX; ring
  have hy : 0*omega.1+nu 1*W*omega.2+ -(nu 1*W*center)=
      nu 1*symbolY W omega.2 center := by unfold symbolY; ring
  rw [hx,hy]
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FrequencyKernelTranslations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier characters translate the actual convolution kernels.
Their translation vectors follow the packet's long and short coordinates. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem planarInverse_modulatedFrequencyWindow (F : SchwartzMap (ℝ×ℝ) ℂ)
    (a b c : ℝ) (x : ℝ×ℝ) :
    planarInverseSchwartz (modulatedFrequencyWindow F a b c) x=
      (Real.fourierChar c:ℂ)*planarInverseSchwartz F (x+(a,b)) := by
  rw [planarInverseSchwartz_apply, planarInverseSchwartz_apply, planarInverse,
    planarInverse, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with omega
  rw [modulatedFrequencyWindow_apply]
  simp only [Circle.smul_def, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  simp only [Real.fourierChar_apply, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem planarInverseSchwartz_smul (c : ℂ) (F : SchwartzMap (ℝ×ℝ) ℂ) (x : ℝ×ℝ) :
    planarInverseSchwartz (c • F) x=c*planarInverseSchwartz F x := by
  rw [planarInverseSchwartz_apply, planarInverseSchwartz_apply]
  exact planarInverse_const_mul c F x

theorem horizontalFrequencyKernel_apply (A : SchwartzMap (ℝ×ℝ) ℂ) (nu : SymbolSpace)
    (q : ℕ) (l theta : ℝ) (x : ℝ×ℝ) :
    horizontalFrequencyKernel A nu q l theta x=
      (symbolWeight q nu:ℂ)*planarInverseSchwartz A (x+(nu 0*l,nu 0*l*theta)) := by
  rw [horizontalFrequencyKernel, planarInverseSchwartz_smul,
    planarInverse_modulatedFrequencyWindow]
  simp only [Real.fourierChar_apply, mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_mul]

theorem verticalFrequencyKernel_apply (B : SchwartzMap (ℝ×ℝ) ℂ) (nu : SymbolSpace)
    (q : ℕ) (W center : ℝ) (x : ℝ×ℝ) :
    verticalFrequencyKernel B nu q W center x=
      (symbolWeight q nu:ℂ)*(Real.fourierChar (-(nu 1*W*center)):ℂ)*
        planarInverseSchwartz B (x+(0,nu 1*W)) := by
  rw [verticalFrequencyKernel, planarInverseSchwartz_smul,
    planarInverse_modulatedFrequencyWindow]
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ModulatedInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint parameter dependence and a uniform bound for the separated
frequency multiplier. These are used to interchange its parameter and
physical-space integrals. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem planarInverse_norm_le (F : ℝ×ℝ → ℂ) (x : ℝ×ℝ) :
    ‖planarInverse F x‖ ≤ ∫ omega, ‖F omega‖ ∂planeMeasure := by
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [] with omega
  simp only [Circle.smul_def,smul_eq_mul,norm_mul,Circle.norm_coe,one_mul]

theorem modulated_inverse_norm_le (F : ℝ×ℝ → ℂ) (nu : SymbolSpace)
    (l W theta center : ℝ) (x : ℝ×ℝ) :
    ‖planarInverse (modulatedFrequency F nu l W theta center) x‖ ≤
      ∫ omega, ‖F omega‖ ∂planeMeasure := by
  apply (planarInverse_norm_le _ x).trans_eq
  apply integral_congr_ae
  filter_upwards [] with omega
  rw [modulatedFrequency,norm_mul,norm_frequencyCharacter,one_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ModulatedInverseL1
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint parameter continuity of the inverse modulated multiplier only
needs integrable frequency data, so it applies to amplitude slices. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem modulated_inverse_joint_continuous_l1 (F : ℝ×ℝ → ℂ)
    (hF : Integrable F planeMeasure) (l W theta center : ℝ) :
    Continuous (fun p : SymbolSpace×(ℝ×ℝ) =>
      planarInverse (modulatedFrequency F p.1 l W theta center) p.2) := by
  unfold planarInverse modulatedFrequency
  apply continuous_of_dominated (bound:=fun omega => ‖F omega‖)
  · intro p
    have hp : Continuous (fun omega : ℝ×ℝ =>
        (Real.fourierChar (p.2.1*omega.1+p.2.2*omega.2):ℂ)*
          frequencyCharacter p.1 (symbolX l omega.1 omega.2 theta) (symbolY W omega.2 center)) := by
      unfold frequencyCharacter symbolX symbolY
      fun_prop
    apply (hp.aestronglyMeasurable.mul hF.aestronglyMeasurable).congr
    filter_upwards [] with omega
    change ((Real.fourierChar (p.2.1*omega.1+p.2.2*omega.2):ℂ)*
      frequencyCharacter p.1 (symbolX l omega.1 omega.2 theta) (symbolY W omega.2 center))*F omega=
      (Real.fourierChar (p.2.1*omega.1+p.2.2*omega.2):ℂ)*
        (frequencyCharacter p.1 (symbolX l omega.1 omega.2 theta) (symbolY W omega.2 center)*F omega)
    ring
  · intro p
    filter_upwards [] with omega
    simp only [Circle.norm_smul,norm_mul,norm_frequencyCharacter,one_mul,le_refl]
  · exact hF.norm
  · filter_upwards [] with omega
    unfold frequencyCharacter symbolX symbolY
    fun_prop

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LocalizedSelectorDerivative
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The separated selector has a derivative bound uniform in the Fourier
parameter. The fixed polynomial weight absorbs its linear growth. -/
noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem selectorCharacter_hasDerivAt (nu : SymbolSpace) (U : ℝ) :
    HasDerivAt (selectorCharacter nu)
      (((2*Real.pi*nu 2 : ℝ):ℂ)*Complex.I*selectorCharacter nu U) U := by
  have h := (Real.hasDerivAt_fourierChar (nu 2*U)).scomp U
    ((hasDerivAt_id U).const_mul (nu 2))
  refine h.congr_deriv ?_
  · simp only [Complex.real_smul, selectorCharacter, mul_one]
    push_cast
    ring

theorem weightedSelector_hasDerivAt (S : SchwartzMap SymbolSpace ℂ)
    (q : ℕ) (nu : SymbolSpace) (U : ℝ) :
    HasDerivAt (weightedSelector S q nu)
      (((2*Real.pi*nu 2 : ℝ):ℂ)*Complex.I*weightedSelector S q nu U) U := by
  refine ((selectorCharacter_hasDerivAt nu U).const_mul
    (𝓕 S nu/((symbolWeight q nu:ℝ):ℂ)^3)).congr_deriv ?_
  · unfold weightedSelector
    ring

theorem symbolWeight_le_one (q : ℕ) (nu : SymbolSpace) : symbolWeight q nu≤1 := by
  simpa only [pow_zero, one_mul] using symbolWeight_coordinate q 0 (Nat.zero_le q) nu 0

theorem weightedSelector_norm_le (S : SchwartzMap SymbolSpace ℂ)
    (q : ℕ) (nu : SymbolSpace) (U : ℝ) :
    ‖weightedSelector S q nu U‖ ≤ symbolCoefficientBound S q :=
  (weightedSelector_bound S q nu U).trans
    ((mul_le_mul_of_nonneg_left (symbolWeight_le_one q nu)
      (symbolCoefficientBound_pos S q).le).trans_eq (mul_one _))

theorem weightedSelector_deriv_bound (S : SchwartzMap SymbolSpace ℂ)
    (q : ℕ) (hq : 1≤q) (nu : SymbolSpace) (U : ℝ) :
    ‖deriv (weightedSelector S q nu) U‖≤2*Real.pi*symbolCoefficientBound S q := by
  have hC : 0 ≤ symbolCoefficientBound S q := (symbolCoefficientBound_pos S q).le
  rw [(weightedSelector_hasDerivAt S q nu U).deriv, norm_mul, norm_mul,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ (2*Real.pi*|nu 2|)*(symbolCoefficientBound S q*symbolWeight q nu) :=
      mul_le_mul_of_nonneg_left (weightedSelector_bound S q nu U) (by positivity)
    _ = (2*Real.pi*symbolCoefficientBound S q)*(|nu 2| * symbolWeight q nu) := by ring
    _ ≤ (2*Real.pi*symbolCoefficientBound S q)*1 :=
      mul_le_mul_of_nonneg_left
        (by simpa only [pow_one] using symbolWeight_coordinate q 1 hq nu 2) (by positivity)
    _ = _ := mul_one _

theorem localizedSelector_deriv_bound (chi : SchwartzMap ℝ ℝ) (hchi : ∀ U, |chi U|≤1)
    (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (hq : 1≤q) (nu : SymbolSpace) (U : ℝ) :
    ‖deriv (localizedSelector chi S q nu) U‖≤
      (SchwartzMap.seminorm ℝ 0 1 chi+2*Real.pi)*symbolCoefficientBound S q := by
  have hd := (chi.hasDerivAt U).ofReal_comp.mul (weightedSelector_hasDerivAt S q nu U)
  change HasDerivAt (localizedSelector chi S q nu) _ U at hd
  rw [hd.deriv]
  have hchi' : ‖deriv chi U‖≤SchwartzMap.seminorm ℝ 0 1 chi := by
    simpa only [iteratedDeriv_one, pow_zero, one_mul] using
      SchwartzMap.le_seminorm' ℝ 0 1 chi U
  calc
    _ ≤ ‖((deriv chi U:ℝ):ℂ)*weightedSelector S q nu U‖+
        ‖(chi U:ℂ)*(((2*Real.pi*nu 2:ℝ):ℂ)*Complex.I*weightedSelector S q nu U)‖ :=
      norm_add_le _ _
    _ = ‖deriv chi U‖*‖weightedSelector S q nu U‖+
        |chi U| * ‖deriv (weightedSelector S q nu) U‖ := by
      rw [← (weightedSelector_hasDerivAt S q nu U).deriv]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ SchwartzMap.seminorm ℝ 0 1 chi*symbolCoefficientBound S q+
        1*(2*Real.pi*symbolCoefficientBound S q) := by
      gcongr
      · exact weightedSelector_norm_le S q nu U
      · exact hchi U
      · exact weightedSelector_deriv_bound S q hq nu U
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_UnitPacketSelector
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact Fourier selectors are normalized to the size and
Lipschitz bounds required by the finite packet model. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem selectorNormalizer_pos (chi : SchwartzMap ℝ ℝ) (C : ℝ) (hC : 0<C) :
    0 < selectorNormalizer chi C := by unfold selectorNormalizer; positivity

theorem unitPacketSelector_differentiable (chi : SchwartzMap ℝ ℝ) (C : ℝ)
    (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (nu : SymbolSpace) :
    Differentiable ℝ (unitPacketSelector chi C S q nu) := by
  intro U
  exact (((chi.hasDerivAt U).ofReal_comp.mul (weightedSelector_hasDerivAt S q nu U)).const_mul
    ((selectorNormalizer chi C)⁻¹:ℂ)).differentiableAt

theorem unitPacketSelector_bound (chi : SchwartzMap ℝ ℝ) (hchi : ∀ U, |chi U|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ)
    (hS : symbolCoefficientBound S q≤C) (nu : SymbolSpace) (U : ℝ) :
    ‖unitPacketSelector chi C S q nu U‖≤1 := by
  have hM := selectorNormalizer_pos chi C hC
  have hCM : C ≤ selectorNormalizer chi C := by
    unfold selectorNormalizer
    nlinarith only [hC, apply_nonneg (SchwartzMap.seminorm ℝ 0 1) chi, Real.pi_pos]
  have hb : ‖localizedSelector chi S q nu U‖≤C :=
    (localizedSelector_bound chi hchi S q nu U).trans
      (((mul_le_mul_of_nonneg_right hS (symbolWeight_pos q nu).le).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (symbolWeight_le_one q nu) hC.le)))
  rw [unitPacketSelector, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  exact (mul_le_mul_of_nonneg_left (hb.trans hCM) (inv_nonneg.mpr hM.le)).trans_eq
    (inv_mul_cancel₀ hM.ne')

theorem unitPacketSelector_deriv_bound (chi : SchwartzMap ℝ ℝ) (hchi : ∀ U, |chi U|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (hq : 1≤q)
    (hS : symbolCoefficientBound S q≤C) (nu : SymbolSpace) (U : ℝ) :
    ‖deriv (unitPacketSelector chi C S q nu) U‖≤1 := by
  have hM := selectorNormalizer_pos chi C hC
  have hd : HasDerivAt (localizedSelector chi S q nu) _ U :=
    (chi.hasDerivAt U).ofReal_comp.mul (weightedSelector_hasDerivAt S q nu U)
  have hc := hd.const_mul ((selectorNormalizer chi C)⁻¹:ℂ)
  change HasDerivAt (unitPacketSelector chi C S q nu) _ U at hc
  rw [hc.deriv, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, ← hd.deriv]
  have hb : ‖deriv (localizedSelector chi S q nu) U‖ ≤ selectorNormalizer chi C := by
    apply (localizedSelector_deriv_bound chi hchi S q hq nu U).trans
    have hnonneg : 0≤SchwartzMap.seminorm ℝ 0 1 chi+2*Real.pi := by positivity
    have h := mul_le_mul_of_nonneg_left hS hnonneg
    unfold selectorNormalizer
    nlinarith only [h,hC]
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hM.le)).trans_eq (inv_mul_cancel₀ hM.ne')

theorem unitPacketSelector_lipschitz (chi : SchwartzMap ℝ ℝ) (hchi : ∀ U, |chi U|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (hq : 1≤q)
    (hS : symbolCoefficientBound S q≤C) (nu : SymbolSpace) :
    LipschitzWith 1 (unitPacketSelector chi C S q nu) := by
  apply lipschitzWith_of_nnnorm_deriv_le (unitPacketSelector_differentiable chi C S q nu)
  intro U
  exact_mod_cast unitPacketSelector_deriv_bound chi hchi C hC S q hq hS nu U

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_UnitConvolutionParameter
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint dependence on the remaining Fourier parameter. These are the
literal kernels and selectors in the packet representation, so their
finite sums may be integrated against the outside symbol weight. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem symbolWeight_continuous (q : ℕ) : Continuous (symbolWeight q) := by
  unfold symbolWeight
  exact ((continuous_const.add continuous_norm).pow q).inv₀
    (fun nu => (pow_pos (by positivity : 0<1+‖nu‖) q).ne')

theorem unitPacketSelector_joint_continuous (chi : SchwartzMap ℝ ℝ) (C : ℝ)
    (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) :
    Continuous (fun p : SymbolSpace×ℝ => unitPacketSelector chi C S q p.1 p.2) := by
  have hw : ∀ p : SymbolSpace×ℝ, ((symbolWeight q p.1:ℝ):ℂ)^3≠0 := by
    intro p
    apply pow_ne_zero
    exact_mod_cast (symbolWeight_pos q p.1).ne'
  have hs : Continuous (fun p : SymbolSpace×ℝ => selectorCharacter p.1 p.2) := by
    unfold selectorCharacter
    fun_prop
  unfold unitPacketSelector localizedSelector weightedSelector
  exact continuous_const.mul ((Complex.continuous_ofReal.comp (chi.continuous.comp continuous_snd)).mul
    ((((𝓕 S : SchwartzMap SymbolSpace ℂ).continuous.comp continuous_fst).div
      ((Complex.continuous_ofReal.comp ((symbolWeight_continuous q).comp continuous_fst)).pow 3) hw).mul hs))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketFrequencyInputL1
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frequency input and exact separated convolution identities for L1
data, including the amplitude slices of the bin decomposition. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem packetFrequencyInputL1_integrable (A B : SchwartzMap (ℝ×ℝ) ℂ)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) :
    Integrable (packetFrequencyInputL1 A B f) planeMeasure := by
  have hAB : Integrable (fun omega => A omega*B omega) planeMeasure :=
    A.integrable.mul_bdd B.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun omega => SchwartzMap.norm_le_seminorm ℝ B omega))
  exact hAB.mul_bdd (planarFourier_l1_continuous f hf).aestronglyMeasurable
    (Filter.Eventually.of_forall (planarFourier_l1_bound f))

theorem frequencyKernel_convolution_l1 (A B : SchwartzMap (ℝ×ℝ) ℂ)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure)
    (nu : SymbolSpace) (q : ℕ) (l W theta center : ℝ) (x : ℝ×ℝ) :
    kernelConvolution (horizontalFrequencyKernel A nu q l theta)
      (kernelConvolution (verticalFrequencyKernel B nu q W center) f) x=
    (symbolWeight q nu:ℂ)^2*
      planarInverse (modulatedFrequency (packetFrequencyInputL1 A B f) nu l W theta center) x := by
  rw [←factored_multiplier_convolution_l1 _ _ f hf]
  simp_rw [frequencyKernel_product]
  rw [←planarInverse_const_mul]
  congr 1
  funext omega
  unfold modulatedFrequency packetFrequencyInputL1
  ring

theorem frequencyKernel_convolution_joint_continuous_l1 (A B : SchwartzMap (ℝ×ℝ) ℂ)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure)
    (q : ℕ) (l W theta center : ℝ) :
    Continuous (fun p : SymbolSpace×(ℝ×ℝ) =>
      kernelConvolution (horizontalFrequencyKernel A p.1 q l theta)
        (kernelConvolution (verticalFrequencyKernel B p.1 q W center) f) p.2) := by
  simp_rw [frequencyKernel_convolution_l1 A B f hf]
  exact ((Complex.continuous_ofReal.comp ((symbolWeight_continuous q).comp continuous_fst)).pow 2).mul
    (modulated_inverse_joint_continuous_l1 (packetFrequencyInputL1 A B f)
      (packetFrequencyInputL1_integrable A B f hf) l W theta center)

theorem unitConvolution_pairing_stronglyMeasurable_l1 (chi : SchwartzMap ℝ ℝ) (C : ℝ)
    (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (A B : SchwartzMap (ℝ×ℝ) ℂ)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure)
    (U : ℝ×ℝ → ℝ) (hU : Measurable U)
    (g : ℝ×ℝ → ℂ) (hg : Measurable g) (l W theta center : ℝ) :
    StronglyMeasurable (fun nu : SymbolSpace => ∫ x,
      unitPacketSelector chi C S q nu (U x)*
        kernelConvolution (horizontalFrequencyKernel A nu q l theta)
          (kernelConvolution (verticalFrequencyKernel B nu q W center) f) x*
        star (g x) ∂planeMeasure) := by
  have hsel : Measurable (fun p : SymbolSpace×(ℝ×ℝ) =>
      unitPacketSelector chi C S q p.1 (U p.2)) :=
    (unitPacketSelector_joint_continuous chi C S q).measurable.comp
      (measurable_fst.prodMk (hU.comp measurable_snd))
  have hker := (frequencyKernel_convolution_joint_continuous_l1 A B f hf q l W theta center).measurable
  have htest : Measurable (fun p : SymbolSpace×(ℝ×ℝ) => star (g p.2)) :=
    continuous_star.measurable.comp (hg.comp measurable_snd)
  exact ((hsel.mul hker).mul htest).stronglyMeasurable.integral_prod_right'

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_UnitConvolutionWeightL1
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An integrable majorant justifying the outside Fourier integral.
This bound is used only for interchanging finite sums and integration;
the uniform model bounds are applied to their complete joint sum. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem unitConvolution_pairing_bound_l1 (chi : SchwartzMap ℝ ℝ) (hchi : ∀ s, |chi s|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ)
    (hS : symbolCoefficientBound S q≤C)
    (A B : SchwartzMap (ℝ×ℝ) ℂ) (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) (U : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → ℂ) (hg : Integrable g planeMeasure)
    (l W theta center : ℝ) (nu : SymbolSpace) :
    ‖∫ x, unitPacketSelector chi C S q nu (U x)*
      kernelConvolution (horizontalFrequencyKernel A nu q l theta)
        (kernelConvolution (verticalFrequencyKernel B nu q W center) f) x*
      star (g x) ∂planeMeasure‖≤
        (∫ omega, ‖packetFrequencyInputL1 A B f omega‖ ∂planeMeasure)*(∫ x, ‖g x‖ ∂planeMeasure) := by
  let M := ∫ omega, ‖packetFrequencyInputL1 A B f omega‖ ∂planeMeasure
  have hkernel (x : ℝ×ℝ) :
      ‖kernelConvolution (horizontalFrequencyKernel A nu q l theta)
        (kernelConvolution (verticalFrequencyKernel B nu q W center) f) x‖≤M := by
    rw [frequencyKernel_convolution_l1 A B f hf,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (symbolWeight_pos q nu)]
    have hw : (symbolWeight q nu)^2≤1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (symbolWeight_pos q nu).le (symbolWeight_le_one q nu) 2
    exact (mul_le_mul hw (modulated_inverse_norm_le (packetFrequencyInputL1 A B f) nu l W theta center x)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul M)
  have hnorm (x : ℝ×ℝ) :
      ‖unitPacketSelector chi C S q nu (U x)*
        kernelConvolution (horizontalFrequencyKernel A nu q l theta)
          (kernelConvolution (verticalFrequencyKernel B nu q W center) f) x*star (g x)‖≤‖g x‖*M := by
    rw [norm_mul,norm_mul,norm_star]
    have hs := unitPacketSelector_bound chi hchi C hC S q hS nu (U x)
    calc
      _ ≤ (1*M)*‖g x‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul hs (hkernel x) (norm_nonneg _) (by norm_num)) (norm_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ∫ x, ‖g x‖*M ∂planeMeasure := norm_integral_le_of_norm_le (hg.norm.mul_const M)
      (Filter.Eventually.of_forall hnorm)
    _ = _ := by rw [integral_mul_const]; ring

theorem unitConvolution_weight_integrable_l1 (chi : SchwartzMap ℝ ℝ) (hchi : ∀ s, |chi s|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (hq : 4≤q)
    (hS : symbolCoefficientBound S q≤C)
    (A B : SchwartzMap (ℝ×ℝ) ℂ) (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) (U : ℝ×ℝ → ℝ) (hU : Measurable U)
    (g : ℝ×ℝ → ℂ) (hgm : Measurable g) (hg : Integrable g planeMeasure)
    (l W theta center : ℝ) :
    Integrable (fun nu : SymbolSpace => (symbolWeight q nu:ℂ)*∫ x,
      unitPacketSelector chi C S q nu (U x)*
        kernelConvolution (horizontalFrequencyKernel A nu q l theta)
          (kernelConvolution (verticalFrequencyKernel B nu q W center) f) x*
        star (g x) ∂planeMeasure) :=
  (symbol_average_bound q hq _
    (unitConvolution_pairing_stronglyMeasurable_l1 chi C S q A B f hf U hU g hgm l W theta center).aestronglyMeasurable
    _ (Filter.Eventually.of_forall (fun nu =>
      unitConvolution_pairing_bound_l1 chi hchi C hC S q hS A B f hf U g hg l W theta center nu))).1

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SeparatedSymbolPairingL1
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier separation of the full bilinear form with a measurable
output-dependent direction. The parameter/space interchange follows
from an explicit integrable product majorant. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem separated_symbol_pairing_l1 (chi : SchwartzMap ℝ ℝ)
    (hchi : ∀ s, |chi s|≤1) (S : SchwartzMap SymbolSpace ℂ)
    (F : ℝ×ℝ → ℂ) (hF : Integrable F planeMeasure) (U : ℝ×ℝ → ℝ) (hU : Measurable U)
    (g : ℝ×ℝ → ℂ) (hgm : Measurable g) (hg : Integrable g planeMeasure)
    (l W theta center : ℝ) :
    (∫ x, (chi (U x):ℂ)*
      (∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (S (symbolPoint (symbolX l omega.1 omega.2 theta)
          (symbolY W omega.2 center) (U x))*F omega) ∂planeMeasure)*conj (g x)
        ∂planeMeasure) =
    ∫ nu : SymbolSpace, ∫ x,
      (chi (U x):ℂ)*(𝓕 S nu*selectorCharacter nu (U x))*
        planarInverse (modulatedFrequency F nu l W theta center) x*conj (g x)
          ∂planeMeasure := by
  let C : ℝ := ∫ omega, ‖F omega‖ ∂planeMeasure
  let phase := fun p : SymbolSpace×(ℝ×ℝ) =>
    (chi (U p.2):ℂ)*selectorCharacter p.1 (U p.2)*
      planarInverse (modulatedFrequency F p.1 l W theta center) p.2
  let H := fun p : SymbolSpace×(ℝ×ℝ) => (𝓕 S p.1*conj (g p.2))*phase p
  have hC : 0≤C := integral_nonneg (fun _ => norm_nonneg _)
  have hphase : Measurable phase := by
    apply Measurable.mul
    · apply Measurable.mul
      · exact Complex.continuous_ofReal.measurable.comp (chi.continuous.measurable.comp
          (hU.comp measurable_snd))
      · have hc : Continuous (fun p : SymbolSpace×ℝ => selectorCharacter p.1 p.2) := by
          unfold selectorCharacter
          fun_prop
        exact hc.measurable.comp (measurable_fst.prodMk (hU.comp measurable_snd))
    · exact (modulated_inverse_joint_continuous_l1 F hF l W theta center).measurable
  have hphaseBound (p : SymbolSpace×(ℝ×ℝ)) : ‖phase p‖≤C := by
    have h₁ : ‖(chi (U p.2):ℂ)‖≤1 := by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using hchi (U p.2)
    have h₂ := modulated_inverse_norm_le F p.1 l W theta center p.2
    dsimp only [phase]
    rw [norm_mul,norm_mul,norm_selectorCharacter,mul_one]
    exact (mul_le_mul h₁ h₂ (norm_nonneg _) (by norm_num)).trans_eq (one_mul C)
  have hHm : Measurable H := by
    apply Measurable.mul
    · exact ((𝓕 S : SchwartzMap SymbolSpace ℂ).continuous.measurable.comp measurable_fst).mul
        (Complex.continuous_conj.measurable.comp (hgm.comp measurable_snd))
    · exact hphase
  have hH : Integrable H (volume.prod planeMeasure) := by
    apply (((𝓕 S : SchwartzMap SymbolSpace ℂ).integrable.norm.mul_prod hg.norm).mul_const C).mono'
      hHm.aestronglyMeasurable
    filter_upwards [] with p
    dsimp only [H]
    rw [norm_mul,norm_mul,RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_left (hphaseBound p) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hleft (x : ℝ×ℝ) :
      (chi (U x):ℂ)*(∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (S (symbolPoint (symbolX l omega.1 omega.2 theta)
          (symbolY W omega.2 center) (U x))*F omega) ∂planeMeasure)*conj (g x) =
        ∫ nu : SymbolSpace, H (nu,x) := by
    rw [separated_symbol_operator S F hF,
      ←integral_const_mul,←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with nu
    dsimp only [H,phase]
    ring
  calc
    _ = ∫ x, (∫ nu : SymbolSpace, H (nu,x)) ∂planeMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall hleft)
    _ = ∫ nu : SymbolSpace, ∫ x, H (nu,x) ∂planeMeasure :=
      (integral_integral_swap hH).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with nu
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [H,phase]
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_UnitSymbolPairingL1
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The separated bilinear form with unit-normalized selectors and the
same two weights already built into the physical wave profiles. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem unit_symbol_pairing_l1 (chi : SchwartzMap ℝ ℝ) (hchi : ∀ s, |chi s|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ)
    (F : ℝ×ℝ → ℂ) (hF : Integrable F planeMeasure) (U : ℝ×ℝ → ℝ) (hU : Measurable U)
    (g : ℝ×ℝ → ℂ) (hgm : Measurable g) (hg : Integrable g planeMeasure)
    (l W theta center : ℝ) :
    (∫ x, (chi (U x):ℂ)*
      (∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (S (symbolPoint (symbolX l omega.1 omega.2 theta)
          (symbolY W omega.2 center) (U x))*F omega) ∂planeMeasure)*conj (g x)
        ∂planeMeasure) =
    (selectorNormalizer chi C:ℂ)*(∫ nu : SymbolSpace, (symbolWeight q nu:ℂ)*
      ∫ x, unitPacketSelector chi C S q nu (U x)*
        planarInverse (fun omega => (symbolWeight q nu:ℂ)^2*
          modulatedFrequency F nu l W theta center omega) x*conj (g x) ∂planeMeasure) := by
  rw [separated_symbol_pairing_l1 chi hchi S F hF U hU g hgm hg l W theta center,
    ←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with nu
  rw [←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [planarInverse_const_mul]
  have hM : (selectorNormalizer chi C:ℂ)≠0 := by
    exact_mod_cast (selectorNormalizer_pos chi C hC).ne'
  have hw : (symbolWeight q nu:ℂ)≠0 := by
    exact_mod_cast (symbolWeight_pos q nu).ne'
  dsimp only [unitPacketSelector,localizedSelector,weightedSelector]
  field_simp

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteUnitSymbolPairingL1
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Fourier separation of a finite sum before applying its model
estimate. All rows share the outside symbol parameter and its weight. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem unit_symbol_convolution_pairing_l1 (chi : SchwartzMap ℝ ℝ) (hchi : ∀ s, |chi s|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ)
    (A B : SchwartzMap (ℝ×ℝ) ℂ) (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) (U : ℝ×ℝ → ℝ) (hU : Measurable U)
    (g : ℝ×ℝ → ℂ) (hgm : Measurable g) (hg : Integrable g planeMeasure)
    (l W theta center : ℝ) :
    (∫ x, (chi (U x):ℂ)*
      (∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (S (symbolPoint (symbolX l omega.1 omega.2 theta)
          (symbolY W omega.2 center) (U x))*
            (A omega*B omega*planarFourier f omega)) ∂planeMeasure)*star (g x)
      ∂planeMeasure) =
    (selectorNormalizer chi C:ℂ)*(∫ nu : SymbolSpace, (symbolWeight q nu:ℂ)*
      ∫ x, unitPacketSelector chi C S q nu (U x)*
        kernelConvolution (horizontalFrequencyKernel A nu q l theta)
          (kernelConvolution (verticalFrequencyKernel B nu q W center) f) x*star (g x)
        ∂planeMeasure) := by
  have h := unit_symbol_pairing_l1 chi hchi C hC S q (packetFrequencyInputL1 A B f)
    (packetFrequencyInputL1_integrable A B f hf)
    U hU g hgm hg l W theta center
  simp only [packetFrequencyInputL1,starRingEnd_apply] at h
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with nu
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  have hk := frequencyKernel_convolution_l1 A B f hf nu q l W theta center x
  rw [←planarInverse_const_mul] at hk
  have he : (fun omega => (symbolWeight q nu:ℂ)^2*
      modulatedFrequency (packetFrequencyInputL1 A B f) nu l W theta center omega)=
      (fun omega => (symbolWeight q nu:ℂ)^2*
        modulatedFrequency (fun omega => A omega*B omega*planarFourier f omega)
          nu l W theta center omega) := by
    funext omega
    simp only [modulatedFrequency,packetFrequencyInputL1]
  rw [he] at hk
  rw [hk,he]

theorem finite_unit_symbol_pairing_l1 {ι : Type*} [Fintype ι]
    (chi : SchwartzMap ℝ ℝ) (hchi : ∀ s, |chi s|≤1) (C : ℝ) (hC : 0<C)
    (S : ι → SchwartzMap SymbolSpace ℂ) (q : ℕ) (hq : 4≤q)
    (hS : ∀ i, symbolCoefficientBound (S i) q≤C)
    (A B : ι → SchwartzMap (ℝ×ℝ) ℂ) (f : ι → ℝ×ℝ → ℂ)
    (hf : ∀ i, Integrable (f i) planeMeasure)
    (U : ι → ℝ×ℝ → ℝ) (hU : ∀ i, Measurable (U i))
    (g : ι → ℝ×ℝ → ℂ) (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, Integrable (g i) planeMeasure) (l W theta center : ι → ℝ) :
    (∑ i, ∫ x, (chi (U i x):ℂ)*
      (∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (S i (symbolPoint (symbolX (l i) omega.1 omega.2 (theta i))
          (symbolY (W i) omega.2 (center i)) (U i x))*
            (A i omega*B i omega*planarFourier (f i) omega)) ∂planeMeasure)*star (g i x)
      ∂planeMeasure) =
    (selectorNormalizer chi C:ℂ)*(∫ nu : SymbolSpace, (symbolWeight q nu:ℂ)*
      ∑ i, ∫ x, unitPacketSelector chi C (S i) q nu (U i x)*
        kernelConvolution (horizontalFrequencyKernel (A i) nu q (l i) (theta i))
          (kernelConvolution (verticalFrequencyKernel (B i) nu q (W i) (center i)) (f i)) x*
        star (g i x) ∂planeMeasure) := by
  let V := fun i nu => ∫ x, unitPacketSelector chi C (S i) q nu (U i x)*
    kernelConvolution (horizontalFrequencyKernel (A i) nu q (l i) (theta i))
      (kernelConvolution (verticalFrequencyKernel (B i) nu q (W i) (center i)) (f i)) x*
    star (g i x) ∂planeMeasure
  have hi (i : ι) : Integrable (fun nu => (symbolWeight q nu:ℂ)*V i nu) volume :=
    unitConvolution_weight_integrable_l1 chi hchi C hC (S i) q hq (hS i) (A i) (B i) (f i) (hf i)
      (U i) (hU i) (g i) (hgm i) (hg i) (l i) (W i) (theta i) (center i)
  calc
    _ = ∑ i, (selectorNormalizer chi C:ℂ)*(∫ nu : SymbolSpace, (symbolWeight q nu:ℂ)*V i nu) :=
      Finset.sum_congr rfl (fun i _ => unit_symbol_convolution_pairing_l1 chi hchi C hC (S i) q
        (A i) (B i) (f i) (hf i) (U i) (hU i) (g i) (hgm i) (hg i) (l i) (W i) (theta i) (center i))
    _ = (selectorNormalizer chi C:ℂ)*(∑ i, ∫ nu : SymbolSpace, (symbolWeight q nu:ℂ)*V i nu) :=
      (Finset.mul_sum _ _ _).symm
    _ = (selectorNormalizer chi C:ℂ)*(∫ nu : SymbolSpace, ∑ i, (symbolWeight q nu:ℂ)*V i nu) := by
      rw [integral_finsetSum _ (fun i _ => hi i)]
    _ = _ := by simp only [Finset.mul_sum,V]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteUnitAverageL1
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the outside Fourier weight to the whole finite convolution
sum. The number of rows never appears in the transferred bound. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem finite_unit_convolution_average_bound_l1 {ι : Type*} [Fintype ι]
    (chi : SchwartzMap ℝ ℝ) (C : ℝ) (hC : 0<C)
    (S : ι → SchwartzMap SymbolSpace ℂ) (q : ℕ) (hq : 4≤q)
    (A B : ι → SchwartzMap (ℝ×ℝ) ℂ) (f : ι → ℝ×ℝ → ℂ)
    (hf : ∀ i, Integrable (f i) planeMeasure)
    (U : ι → ℝ×ℝ → ℝ) (hU : ∀ i, Measurable (U i))
    (g : ι → ℝ×ℝ → ℂ) (hgm : ∀ i, Measurable (g i)) (l W theta center : ι → ℝ)
    (bound : ℝ) :
    let V := fun i nu => ∫ x, unitPacketSelector chi C (S i) q nu (U i x)*
      kernelConvolution (horizontalFrequencyKernel (A i) nu q (l i) (theta i))
        (kernelConvolution (verticalFrequencyKernel (B i) nu q (W i) (center i)) (f i)) x*
      star (g i x) ∂planeMeasure
    (∀ nu : SymbolSpace, ‖∑ i, V i nu‖≤bound) →
    ‖(selectorNormalizer chi C:ℂ)*(∫ nu : SymbolSpace,
      (symbolWeight q nu:ℂ)*(∑ i, V i nu))‖≤
        selectorNormalizer chi C*bound*(∫ nu : SymbolSpace, symbolWeight q nu) := by
  intro V hbound
  have hm : StronglyMeasurable (fun nu : SymbolSpace => ∑ i, V i nu) :=
    Finset.stronglyMeasurable_fun_sum Finset.univ (fun i _ =>
      unitConvolution_pairing_stronglyMeasurable_l1 chi C (S i) q (A i) (B i) (f i) (hf i)
        (U i) (hU i) (g i) (hgm i) (l i) (W i) (theta i) (center i))
  have h := symbol_average_bound q hq _ hm.aestronglyMeasurable bound
    (Filter.Eventually.of_forall hbound)
  have hpos := selectorNormalizer_pos chi C hC
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpos]
  exact (mul_le_mul_of_nonneg_left h.2 hpos.le).trans_eq (by ring)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_JointPacketAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite collection of translated packet lattices is averaged as
one form. The finite-form estimate is applied before integration, so no
factor for the number of length/direction labels is introduced. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

theorem joint_packet_average_bound {ι : Type*} [Fintype ι]
    (μ : ι → Measure (ℝ×ℝ)) [∀ i, IsProbabilityMeasure (μ i)]
    (value : ι → (ℝ×ℝ) → ℂ)
    (hvalue : ∀ i, Integrable (value i) (μ i))
    (term : ι → (ℝ×ℝ) → (ℤ×ℤ) → ℂ)
    (hseries : ∀ i, ∀ᵐ z ∂μ i,
      Summable (fun n => ‖term i z n‖) ∧ (∑' n, term i z n) = value i z)
    (C : ℝ)
    (hfinite : ∀ z : ι → (ℝ×ℝ), ∀ S : Finset (ι×(ℤ×ℤ)),
      ‖∑ p ∈ S, term p.1 (z p.1) p.2‖ ≤ C) :
    ‖∑ i, ∫ z, value i z ∂μ i‖ ≤ C := by
  classical
  have hjoint : ∀ᵐ z : ι → (ℝ×ℝ) ∂Measure.pi μ, ∀ i,
      Summable (fun n => ‖term i (z i) n‖) ∧
        (∑' n, term i (z i) n) = value i (z i) := by
    apply ae_all_iff.mpr
    intro i
    have hi := hseries i
    rw [← (measurePreserving_eval μ i).map_eq] at hi
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hi
  have hbound : ∀ᵐ z : ι → (ℝ×ℝ) ∂Measure.pi μ,
      ‖∑ i, value i (z i)‖ ≤ C := by
    filter_upwards [hjoint] with z hz
    have hn : Summable (fun p : ι×(ℤ×ℤ) => ‖term p.1 (z p.1) p.2‖) :=
      (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
        ⟨fun i => (hz i).1, (hasSum_fintype _).summable⟩
    have hs : Summable (fun p : ι×(ℤ×ℤ) => term p.1 (z p.1) p.2) := hn.of_norm
    have heq : (∑' p : ι×(ℤ×ℤ), term p.1 (z p.1) p.2) =
        ∑ i, value i (z i) := hs.tsum_prod.trans (by
      rw [tsum_fintype]
      exact Finset.sum_congr rfl (fun i _ => (hz i).2))
    rw [← heq]
    exact le_of_tendsto hs.hasSum.norm (Eventually.of_forall (hfinite z))
  have heq : (∫ z : ι → (ℝ×ℝ), ∑ i, value i (z i) ∂Measure.pi μ) =
      ∑ i, ∫ z, value i z ∂μ i := by
    rw [integral_finsetSum _ (fun i _ => integrable_comp_eval (hvalue i))]
    exact Finset.sum_congr rfl (fun i _ => integral_comp_eval (hvalue i).aestronglyMeasurable)
  rw [← heq]
  simpa using norm_integral_le_of_norm_le_const hbound

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_JointLatticeAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete finite length/direction sum can use one product
probability average of the actual translated lattices. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lattice_periodization_integrable {l W theta : ℝ} (hl : 0<l) (hW : 0<W)
    (F : ℝ×ℝ → ℂ) (hF : Integrable F planeMeasure) :
    Integrable (fun z => ∑' n : ℤ×ℤ, F (latticeHom l W theta n+z))
      (latticeAverage l W theta) := by
  let G := (latticeHom l W theta).range
  let e : (ℤ×ℤ) ≃+ G :=
    AddMonoidHom.ofInjective (latticeHom_injective (theta := theta) hl.ne' hW.ne')
  let : Countable G := Countable.of_equiv (ℤ×ℤ) e.toEquiv
  have hm (n : ℤ×ℤ) : AEMeasurable (fun z => F (latticeHom l W theta n+z))
      (planeMeasure.restrict (latticeCell l W theta)) :=
    ((hF.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_add_left planeMeasure (latticeHom l W theta n))).restrict).aemeasurable
  have hmg (g : G) : AEMeasurable (fun z => ‖F (g+ᵥz)‖ₑ)
      (planeMeasure.restrict (latticeCell l W theta)) :=
    ((hF.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_add_left planeMeasure (g:ℝ×ℝ))).restrict).enorm
  have hfinite : (∫⁻ z in latticeCell l W theta,
      ∑' n : ℤ×ℤ, ‖F (latticeHom l W theta n+z)‖ₑ ∂planeMeasure) < ∞ := by
    have heq (z : ℝ×ℝ) : (∑' n : ℤ×ℤ, ‖F (latticeHom l W theta n+z)‖ₑ) =
        ∑' g : G, ‖F (g+ᵥz)‖ₑ :=
      e.toEquiv.tsum_eq (fun g : G => ‖F (g+ᵥz)‖ₑ)
    simp_rw [heq]
    rw [lintegral_tsum hmg, ← (latticeCell_fundamental (theta := theta) hl hW).lintegral_eq_tsum'' (fun z => ‖F z‖ₑ)]
    exact hF.hasFiniteIntegral
  have hi : Integrable (fun z => ∑' n : ℤ×ℤ, F (latticeHom l W theta n+z))
      (planeMeasure.restrict (latticeCell l W theta)) := by
    refine ⟨(AEMeasurable.tsum hm).aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt (lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)) hfinite
  exact hi.smul_measure (by
    exact ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos hl hW))))

theorem joint_lattice_average_bound {ι : Type*} [Fintype ι]
    (l W theta : ι → ℝ) (hl : ∀ i, 0<l i) (hW : ∀ i, 0<W i)
    (F : ι → (ℝ×ℝ) → ℂ) (hF : ∀ i, Integrable (F i) planeMeasure)
    (C : ℝ)
    (hfinite : ∀ z : ι → (ℝ×ℝ), ∀ S : Finset (ι×(ℤ×ℤ)),
      ‖∑ p ∈ S, ((l p.1*W p.1:ℝ):ℂ)⁻¹*
        F p.1 (latticeHom (l p.1) (W p.1) (theta p.1) p.2+z p.1)‖ ≤ C) :
    ‖∑ i, (((l i*W i:ℝ):ℂ)^2)⁻¹ * ∫ z, F i z ∂planeMeasure‖ ≤ C := by
  let μ := fun i => latticeAverage (l i) (W i) (theta i)
  let value := fun i z => ∑' n : ℤ×ℤ, ((l i*W i:ℝ):ℂ)⁻¹*
    F i (latticeHom (l i) (W i) (theta i) n+z)
  let term := fun i z n => ((l i*W i:ℝ):ℂ)⁻¹*
    F i (latticeHom (l i) (W i) (theta i) n+z)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => latticeAverage_probability (hl i) (hW i)
  have hvalue (i : ι) : Integrable (value i) (μ i) := by
    dsimp only [value, μ]
    simp_rw [tsum_mul_left]
    exact (lattice_periodization_integrable (hl i) (hW i) (F i) (hF i)).const_mul _
  have hseries (i : ι) : ∀ᵐ z ∂μ i,
      Summable (fun n => ‖term i z n‖) ∧ (∑' n, term i z n) = value i z := by
    filter_upwards [sheared_lattice_summable (hl i) (hW i) (F i) (hF i)] with z hz
    refine ⟨?_, rfl⟩
    simpa only [term, norm_mul] using hz.mul_left ‖((l i*W i:ℝ):ℂ)⁻¹‖
  have h := joint_packet_average_bound μ value hvalue term hseries C hfinite
  have heq (i : ι) : (∫ z, value i z ∂μ i) =
      (((l i*W i:ℝ):ℂ)^2)⁻¹ * ∫ z, F i z ∂planeMeasure := by
    dsimp only [μ, value]
    rw [integral_latticeAverage (hl i) (hW i)]
    simp_rw [tsum_mul_left]
    rw [integral_const_mul, ← sheared_lattice_periodization (hl i) (hW i) (F i) (hF i)]
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul, pow_two, mul_inv_rev]
    ring
  simpa only [heq] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_FinitePacketSites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Any finite collection in the joint spatial lattice is realized by
finite site fibers. No rectangular truncation or extra packet is added. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {Label : Fin N → Type} (labels : ∀ j, Finset (Label j))

theorem sum_joint_lattice_sites {E : Type*} [AddCommMonoid E]
    (S : Finset (LatticeRow labels × (ℤ×ℤ))) (f : LatticeSiteIndex labels → E) :
    (∑ s∈S.map (latticeSiteProductEquiv labels).symm.toEmbedding, f s) =
      ∑ p∈S, f ((latticeSiteProductEquiv labels).symm p) :=
  Finset.sum_map _ _ _

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FrequencyProfileNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! In the packet coordinates the two Fourier modulations are just
weighted translations of the unmodulated profile. The vertical carrier
phase cancels exactly. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem packetCoordinates_symm_apply (l W theta : ℝ) (hl : l≠0) (hW : W≠0)
    (z : ℝ×ℝ) : (packetCoordinates l W theta hl hW).symm z=
      (l*z.1,W*z.2+theta*(l*z.1)) := rfl

theorem weightedTranslatedProfile_apply (F : SchwartzMap (ℝ×ℝ) ℂ)
    (q : ℕ) (nu : SymbolSpace) (a x : ℝ×ℝ) :
    weightedTranslatedProfile F q nu a x=(symbolWeight q nu:ℂ)*F (x-a) := by
  rw [weightedTranslatedProfile, smul_apply, SchwartzMap.compSubConstCLM_apply]
  rfl

theorem horizontalFrequencyProfile_eq (A : SchwartzMap (ℝ×ℝ) ℂ) (nu : SymbolSpace)
    (q : ℕ) (l W theta carrier : ℝ) (hl : l≠0) (hW : W≠0) :
    convolutionProfile (horizontalFrequencyKernel A nu q l theta) l W theta carrier hl hW=
      weightedTranslatedProfile
        (convolutionProfile (planarInverseSchwartz A) l W theta carrier hl hW)
          q nu (-nu 0,0) := by
  ext z
  rw [weightedTranslatedProfile_apply, convolutionProfile_apply,
    horizontalFrequencyKernel_apply, convolutionProfile_apply]
  have harg : (packetCoordinates l W theta hl hW).symm z+(nu 0*l,nu 0*l*theta)=
      (packetCoordinates l W theta hl hW).symm (z-(-nu 0,0)) := by
    rw [packetCoordinates_symm_apply, packetCoordinates_symm_apply]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  rw [harg]
  simp only [Prod.snd_sub, sub_zero]
  ring

theorem verticalFrequencyProfile_eq (B : SchwartzMap (ℝ×ℝ) ℂ) (nu : SymbolSpace)
    (q : ℕ) (l W theta center : ℝ) (hl : l≠0) (hW : W≠0) :
    convolutionProfile (verticalFrequencyKernel B nu q W center)
        l W theta (2*Real.pi*center) hl hW=
      weightedTranslatedProfile
        (convolutionProfile (planarInverseSchwartz B) l W theta (2*Real.pi*center) hl hW)
          q nu (0,-nu 1) := by
  ext z
  rw [weightedTranslatedProfile_apply, convolutionProfile_apply,
    verticalFrequencyKernel_apply, convolutionProfile_apply]
  have harg : (packetCoordinates l W theta hl hW).symm z+(0,nu 1*W)=
      (packetCoordinates l W theta hl hW).symm (z-(0,-nu 1)) := by
    rw [packetCoordinates_symm_apply, packetCoordinates_symm_apply]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  rw [harg]
  simp only [Prod.snd_sub, sub_neg_eq_add]
  have hphase :
      Complex.exp (((-(2*Real.pi*center*W)*z.2:ℝ):ℂ)*Complex.I)*
        (Real.fourierChar (-(nu 1*W*center)):ℂ)=
      Complex.exp (((-(2*Real.pi*center*W)*(z.2+nu 1):ℝ):ℂ)*Complex.I) := by
    rw [Real.fourierChar_apply, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (symbolWeight q nu:ℂ)*(l*W:ℂ)*
      (Complex.exp (((-(2*Real.pi*center*W)*z.2:ℝ):ℂ)*Complex.I)*
        (Real.fourierChar (-(nu 1*W*center)):ℂ))*
          planarInverseSchwartz B ((packetCoordinates l W theta hl hW).symm (z-(0,-nu 1))) := by ring
    _ = _ := by rw [hphase]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ScaledFrequencyWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frequency windows obtained from a fixed normalized packet profile.
The normalization is exact and removes all spatial scale parameters. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem scaledFrequencyWindow_inverse (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta carrier : ℝ) (hl : l≠0) (hW : W≠0) :
    planarInverseSchwartz (scaledFrequencyWindow F l W theta carrier hl hW)=
      normalizedSpatialKernel F l W theta carrier hl hW := by
  ext x
  rw [planarInverseSchwartz_apply]
  have he : (scaledFrequencyWindow F l W theta carrier hl hW : ℝ×ℝ → ℂ)=
      planarFourier (normalizedSpatialKernel F l W theta carrier hl hW) :=
    funext (planarFourierSchwartz_apply _)
  rw [he]
  exact planarFourier_inversion _ x

theorem normalizedSpatialKernel_profile (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta carrier : ℝ) (hl : l≠0) (hW : W≠0) :
    convolutionProfile (normalizedSpatialKernel F l W theta carrier hl hW)
      l W theta carrier hl hW=F := by
  ext z
  rw [convolutionProfile_apply]
  simp only [normalizedSpatialKernel, smul_apply, smul_eq_mul]
  rw [physicalPlanarPacket_apply, packetCoordinates_symm_apply]
  simp only [sub_zero]
  have hy : (W*z.2+theta*(l*z.1))-theta*(l*z.1)=W*z.2 := by ring
  rw [hy]
  have hz1 : l*z.1/l=z.1 := by field_simp
  have hz2 : W*z.2/W=z.2 := by field_simp
  rw [hz1,hz2]
  have he : Complex.exp (((-(carrier*W)*z.2:ℝ):ℂ)*Complex.I)*
      Complex.exp (((carrier*(W*z.2):ℝ):ℂ)*Complex.I)=1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring
  have harea : (l*W:ℂ)≠0 := by exact_mod_cast mul_ne_zero hl hW
  calc
    _ = ((l*W:ℂ)*(l*W:ℂ)⁻¹)*
        (Complex.exp (((-(carrier*W)*z.2:ℝ):ℂ)*Complex.I)*
          Complex.exp (((carrier*(W*z.2):ℝ):ℂ)*Complex.I))*F z := by ring
    _ = F z := by rw [mul_inv_cancel₀ harea, he, one_mul, one_mul]

theorem scaledFrequencyWindow_profile (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta carrier : ℝ) (hl : l≠0) (hW : W≠0) :
    convolutionProfile (planarInverseSchwartz (scaledFrequencyWindow F l W theta carrier hl hW))
      l W theta carrier hl hW=F := by
  rw [scaledFrequencyWindow_inverse, normalizedSpatialKernel_profile]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnalyzingProfileNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The analyzing wave uses reflection and conjugation together. Its
positive carrier is unchanged, and its normalized profile has the same
uniform weighted-translation bounds as the synthesizing profile. -/
noncomputable section
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem reflectedConjugateProfile_apply (F : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    reflectedConjugateProfile F z=conj (F (-z)) := rfl

theorem reflectedConjugateProfile_weightedTranslate (F : SchwartzMap (ℝ×ℝ) ℂ)
    (q : ℕ) (nu : SymbolSpace) (a : ℝ×ℝ) :
    reflectedConjugateProfile (weightedTranslatedProfile F q nu a)=
      weightedTranslatedProfile (reflectedConjugateProfile F) q nu (-a) := by
  ext z
  simp only [reflectedConjugateProfile_apply, weightedTranslatedProfile_apply,
    map_mul, Complex.conj_ofReal]
  congr 2
  abel_nf

theorem physical_reflectedConjugateProfile (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta carrier : ℝ) (hl : l≠0) (hW : W≠0) (z x : ℝ×ℝ) :
    physicalPlanarPacket (reflectedConjugateProfile F) z.1 z.2 l W theta carrier hl hW x=
      conj (physicalPlanarPacket F 0 0 l W theta carrier hl hW (z-x)) := by
  rw [physicalPlanarPacket_apply, reflectedConjugateProfile_apply, physicalPlanarPacket_apply,
    map_mul, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Prod.fst_sub, Prod.snd_sub, sub_zero]
  have harg : -((x.1-z.1)/l,((x.2-z.2)-theta*(x.1-z.1))/W)=
      ((z.1-x.1)/l,((z.2-x.2)-theta*(z.1-x.1))/W) := by
    ext <;> simp only [Prod.fst_neg, Prod.snd_neg] <;> ring
  rw [harg]
  congr 2
  push_cast
  ring

theorem physical_analyzing_packet (K : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta carrier : ℝ) (hl : l≠0) (hW : W≠0) (z x : ℝ×ℝ) :
    physicalPlanarPacket
      (reflectedConjugateProfile (convolutionProfile K l W theta carrier hl hW))
        z.1 z.2 l W theta carrier hl hW x=analyzingWave (l*W) K z x := by
  rw [physical_reflectedConjugateProfile,
    physical_convolution_packet K l W theta carrier hl hW (0,0) (z-x)]
  simp only [synthesisWave, analyzingWave, show (0,0)=(0:ℝ×ℝ) from rfl,
    sub_zero, map_mul, Complex.conj_ofReal]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_NormalizedPacketProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single Fourier parameter determines both normalized wave profiles.
Their common bound is chosen before all spatial scales and frequency bins. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem synthesisProfile_eq (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
    (l W theta center : ℝ) (hl : l≠0) (hW : W≠0) :
    synthesisProfile F q nu = convolutionProfile
      (horizontalFrequencyKernel
        (scaledFrequencyWindow F l W theta (2*Real.pi*center) hl hW) nu q l theta)
      l W theta (2*Real.pi*center) hl hW := by
  rw [horizontalFrequencyProfile_eq, scaledFrequencyWindow_profile]
  rfl

theorem analysisProfile_eq (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
    (l W theta center : ℝ) (hl : l≠0) (hW : W≠0) :
    analysisProfile F q nu = reflectedConjugateProfile (convolutionProfile
      (verticalFrequencyKernel
        (scaledFrequencyWindow F l W theta (2*Real.pi*center) hl hW) nu q W center)
      l W theta (2*Real.pi*center) hl hW) := by
  rw [verticalFrequencyProfile_eq, scaledFrequencyWindow_profile,
    reflectedConjugateProfile_weightedTranslate]
  simp only [analysisProfile, Prod.neg_mk, neg_zero, neg_neg]

theorem physical_synthesisProfile (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
    (l W theta center : ℝ) (hl : l≠0) (hW : W≠0) (z x : ℝ×ℝ) :
    physicalPlanarPacket (synthesisProfile F q nu) z.1 z.2
      l W theta (2*Real.pi*center) hl hW x =
    synthesisWave (l*W) (horizontalFrequencyKernel
      (scaledFrequencyWindow F l W theta (2*Real.pi*center) hl hW) nu q l theta) z x := by
  rw [synthesisProfile_eq F q nu l W theta center hl hW,
    physical_convolution_packet]

theorem physical_analysisProfile (G : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
    (l W theta center : ℝ) (hl : l≠0) (hW : W≠0) (z x : ℝ×ℝ) :
    physicalPlanarPacket (analysisProfile G q nu) z.1 z.2
      l W theta (2*Real.pi*center) hl hW x =
    analyzingWave (l*W) (verticalFrequencyKernel
      (scaledFrequencyWindow G l W theta (2*Real.pi*center) hl hW) nu q W center) z x := by
  rw [analysisProfile_eq G q nu l W theta center hl hW,
    physical_analyzing_packet]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_NormalizedPacketLattice
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Fourier-separated synthesis profiles on arbitrary finite
translated lattices. The slopes have no global shear restriction. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
  (topLength width scale ratioBound C : ℝ) (order : ℕ)
  (htop : 0<topLength) (hwidth : 0<width) (hC : 0<C) (horder : 3≤order)
  (hratio : 1 ≤ ratioBound) (hscale : |scale/width| ≤ ratioBound)
  (labels : ∀ j, Finset (Label j))
  (originX originZ theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
  (site : ∀ j (l : labels j), Item j l → ℤ×ℤ)
  (hinj : ∀ j l, Function.Injective (site j l))
  (hprofile : planarProfileConstant (synthesisProfile F q nu) (2*order) ≤ C)

local notation "P" => normalizedPacketLattice F q nu topLength width scale ratioBound C order
  htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile

theorem normalizedPacketLattice_synthesis (j : Fin N) (l : labels j)
    (u : Item j l) (k : κ) (x : ℝ×ℝ) :
    (P).physicalPacket 0 j l u k x =
      synthesisWave ((P).length j*width)
        (horizontalFrequencyKernel
          (scaledFrequencyWindow F ((P).length j) width (theta j l) (2*Real.pi*center k)
            ((P).length_pos j).ne' hwidth.ne') nu q ((P).length j) (theta j l))
        ((P).actualX j l u,(P).actualZ j l u) x := by
  change physicalPlanarPacket (synthesisProfile F q nu) _ (_+0*_)
    ((P).length j) width (0+theta j l) (2*Real.pi*center k) _ _ x = _
  simp only [zero_mul, add_zero, zero_add]
  exact physical_synthesisProfile F q nu ((P).length j) width (theta j l) (center k)
    ((P).length_pos j).ne' hwidth.ne' ((P).actualX j l u,(P).actualZ j l u) x

theorem normalizedAnalysisFamily_packet (G : SchwartzMap (ℝ×ℝ) ℂ)
    (j : Fin N) (l : labels j) (u : Item j l) (k : κ) (x : ℝ×ℝ) :
    physicalPlanarPacket
      (normalizedAnalysisFamily F q nu topLength width scale ratioBound C order
        htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile G j l u k)
      ((P).actualX j l u) ((P).actualZ j l u) ((P).length j) width (theta j l)
        (2*Real.pi*center k) ((P).length_pos j).ne' hwidth.ne' x =
      analyzingWave ((P).length j*width)
        (verticalFrequencyKernel
          (scaledFrequencyWindow G ((P).length j) width (theta j l) (2*Real.pi*center k)
            ((P).length_pos j).ne' hwidth.ne') nu q width (center k))
        ((P).actualX j l u,(P).actualZ j l u) x := by
  exact physical_analysisProfile G q nu ((P).length j) width (theta j l) (center k)
    ((P).length_pos j).ne' hwidth.ne' ((P).actualX j l u,(P).actualZ j l u) x

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnalyzingBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite synthesis/analysis duality with arbitrary synthesizing coefficients. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert

theorem finite_analyzing_pairing {X I K : Type*} [MeasurableSpace X] [Fintype K]
    (mu : Measure X) (area : I → ℝ) (wave : I → K → X → ℂ)
    (g : X → EuclideanSpace ℂ K) (c : I → EuclideanSpace ℂ K) (S : Finset I)
    (ha : ∀ i∈S, area i≠0)
    (hint : ∀ i∈S, ∀ k, Integrable (fun x => g x k*conj (wave i k x)) mu) :
    (∫ x, inner ℂ (∑ i∈S, WithLp.toLp 2 (fun k => c i k*wave i k x)) (g x) ∂mu)=
      ∑ i∈S, (area i:ℂ)*inner ℂ (c i) (analyzingCoefficient mu area wave g i) := by
  have hterm (i : I) (hi : i∈S) :
      (area i:ℂ)*inner ℂ (c i) (analyzingCoefficient mu area wave g i)=
        ∑ k, conj (c i k)*(∫ x, g x k*conj (wave i k x) ∂mu) := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have harea : (area i:ℂ)*analyzingCoefficient mu area wave g i k=
        ∫ x, g x k*conj (wave i k x) ∂mu := by
      change (area i:ℂ)*(((area i)⁻¹:ℂ)*_)=_
      rw [←mul_assoc,mul_inv_cancel₀ (by exact_mod_cast ha i hi),one_mul]
    rw [←harea]
    ring
  have hInt (i : I) (hi : i∈S) (k : K) :
      Integrable (fun x => conj (c i k)*(g x k*conj (wave i k x))) mu :=
    (hint i hi k).const_mul _
  symm
  calc
    _ = ∑ i∈S, ∑ k, conj (c i k)*(∫ x, g x k*conj (wave i k x) ∂mu) :=
      Finset.sum_congr rfl hterm
    _ = ∫ x, ∑ i∈S, ∑ k, conj (c i k)*(g x k*conj (wave i k x)) ∂mu := by
      simp_rw [←integral_const_mul]
      rw [integral_finsetSum S (fun i hi => integrable_finsetSum _ (fun k _ => hInt i hi k))]
      apply Finset.sum_congr rfl
      intro i hi
      exact (integral_finsetSum Finset.univ (fun k _ => hInt i hi k)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [PiLp.inner_apply,RCLike.inner_apply,WithLp.ofLp_sum,Finset.sum_apply,
        map_sum,map_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeightIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability and exact area scaling for the actual decaying top weights. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

theorem planeDivide_apply (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (z : ℝ × ℝ) :
    planeDivide a b ha hb z = (z.1 / a, z.2 / b) := by
  rfl

theorem map_planeDivide (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Measure.map (planeDivide a b ha hb) (volume.prod volume) =
      (ENNReal.ofReal |a| * ENNReal.ofReal |b|) • (volume.prod volume) := by
  have hmap (c : ℝ) (hc : c ≠ 0) :
      Measure.map (fun x : ℝ => x * c⁻¹) volume = ENNReal.ofReal |c| • volume := by
    simpa only [smul_eq_mul, Module.finrank_self, pow_one, inv_inv, mul_comm] using
      (Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) (inv_ne_zero hc))
  change Measure.map (Prod.map (fun x => x * a⁻¹) (fun y => y * b⁻¹)) _ = _
  rw [← Measure.map_prod_map volume volume (by fun_prop) (by fun_prop), hmap a ha, hmap b hb,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

theorem integrable_planeDivide (f : ℝ × ℝ → ℝ)
    (hf : Integrable f (volume.prod volume)) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable (fun z => f (planeDivide a b ha hb z)) (volume.prod volume) := by
  apply (integrable_map_equiv (planeDivide a b ha hb) f).mp
  rw [map_planeDivide]
  exact hf.smul_measure (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

theorem integral_planeDivide (f : ℝ × ℝ → ℝ) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∫ z, f (planeDivide a b ha hb z) ∂volume.prod volume) =
      (|a| * |b|) * ∫ z, f z ∂volume.prod volume := by
  rw [← integral_map_equiv (planeDivide a b ha hb), map_planeDivide, integral_smul_measure]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

theorem topProfile_nonnegative (D : ℝ) (z : ℝ × ℝ) : 0 ≤ topProfile D z :=
  Real.rpow_nonneg (by positivity) _

theorem topProfile_continuous (D : ℝ) : Continuous (topProfile D) := by
  unfold topProfile
  apply Continuous.rpow_const (by fun_prop)
  intro z
  left
  positivity

/-- The fixed normalized profile is integrable once its decay exponent exceeds
its two-dimensional domain. -/
theorem topProfile_integrable {D : ℝ} (hD : 2 < D) :
    Integrable (topProfile D) (volume.prod volume) := by
  have hd : (Module.finrank ℝ (ℝ × ℝ) : ℝ) < D := by simpa using hD
  have h := integrable_one_add_norm (μ := (volume.prod volume)) hd
  apply h.mono' (topProfile_continuous D).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (topProfile_nonnegative D z)]
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  simp only [Prod.norm_def, Real.norm_eq_abs]
  have hmax : max |z.1| |z.2| ≤ |z.1| + |z.2| :=
    max_le (by linarith [abs_nonneg z.2]) (by linarith [abs_nonneg z.1])
  linarith

namespace SlopeBox

theorem normalizedCoordinates_eq (T : SlopeBox) (K : ℝ) (hK : 0 < K) (z : ℝ × ℝ) :
    T.normalizedCoordinates K hK z = (T.horizontal z / K, T.transverse z / K) := by
  ext <;> simp [normalizedCoordinates, planeDivide_apply, slopeShear, horizontal, transverse]
  <;> ring

theorem weight_eq_topProfile (T : SlopeBox) (K D : ℝ) (hK : 0 < K) (z : ℝ × ℝ) :
    T.weight K D z = 2 ^ D * topProfile D (T.normalizedCoordinates K hK z) := by
  rw [normalizedCoordinates_eq]
  simp only [weight, topProfile, radius, abs_div, abs_of_pos hK, add_div]

/-- The actual top weight is integrable, uniformly over positions and slopes. -/
theorem weight_integrable (T : SlopeBox) {K D : ℝ} (hK : 0 < K) (hD : 2 < D) :
    Integrable (T.weight K D) (volume.prod volume) := by
  have hf := integrable_planeDivide (topProfile D) (topProfile_integrable hD)
    (K * T.length) (K * T.width)
    (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne')
  have hs := (slopeShear_measurePreserving (-T.slope)).integrable_comp_of_integrable hf
  have ht := hs.comp_sub_right (T.x, T.y)
  have heq : T.weight K D = fun z => 2 ^ D *
      ((fun z => topProfile D (planeDivide (K * T.length) (K * T.width)
        (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)) ∘
        slopeShear (-T.slope)) (z - (T.x, T.y)) := by
    funext z
    exact T.weight_eq_topProfile K D hK z
  rw [heq]
  exact ht.const_mul _

/-- Exact area scaling: all dependence on the box and the dilation is
`K² * length * width`, while the remaining integral is a fixed constant. -/
theorem integral_weight (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) :
    (∫ z, T.weight K D z ∂volume.prod volume) =
      (2 ^ D * ∫ z, topProfile D z ∂volume.prod volume) *
        K ^ 2 * T.length * T.width := by
  have heq : T.weight K D = fun z => 2 ^ D *
      ((fun z => topProfile D (planeDivide (K * T.length) (K * T.width)
        (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)) ∘
        slopeShear (-T.slope)) (z - (T.x, T.y)) := by
    funext z
    exact T.weight_eq_topProfile K D hK z
  rw [heq, integral_const_mul, integral_sub_right_eq_self]
  simp only [Function.comp_apply]
  rw [integral_slopeShear (-T.slope) (fun z => topProfile D
    (planeDivide (K * T.length) (K * T.width)
      (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)),
    integral_planeDivide, abs_of_pos (mul_pos hK T.length_pos),
    abs_of_pos (mul_pos hK T.width_pos)]
  ring

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The density kernel has a quantitative tail outside a dilated slope
box. This turns a weighted density test into the unweighted witness used
by the finite keeper construction. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace LipschitzHilbert
namespace SlopeBox

theorem densityKernel_nonneg (T : SlopeBox) (D : ℝ) (z : ℝ×ℝ) :
    0 ≤ T.densityKernel D z := Real.rpow_nonneg (by linarith [T.radius_nonnegative z]) _

theorem densityKernel_eq_weight (T : SlopeBox) (D : ℝ) (z : ℝ×ℝ) :
    T.densityKernel D z = ((2:ℝ)^D)⁻¹*T.weight 1 D z := by
  have htwo : (2:ℝ)^D ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) D).ne'
  simp only [densityKernel,weight,div_one,←mul_assoc,inv_mul_cancel₀ htwo,one_mul]

theorem densityKernel_integrable (T : SlopeBox) {D : ℝ} (hD : 2 < D) :
    Integrable (T.densityKernel D) (volume.prod volume) := by
  have h := (T.weight_integrable (by norm_num : (0:ℝ)<1) hD).const_mul (((2:ℝ)^D)⁻¹)
  exact h.congr (Eventually.of_forall (fun z => (T.densityKernel_eq_weight D z).symm))

theorem integral_densityKernel (T : SlopeBox) (D : ℝ) :
    (∫ z, T.densityKernel D z ∂volume.prod volume) =
      (∫ z, topProfile D z ∂volume.prod volume)*T.area := by
  simp_rw [T.densityKernel_eq_weight D]
  rw [integral_const_mul,T.integral_weight (by norm_num : (0:ℝ)<1) D]
  have htwo : (2:ℝ)^D ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) D).ne'
  simp only [one_pow,mul_one,SlopeBox.area]
  field_simp [htwo]

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary density is the supremum of the manuscript's actual
weighted box tests. Exceeding a threshold supplies a concrete test, which
can then be fed to the finite keeper construction. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem densityAverage_le (T : SlopeBox) (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ)
    (omega : Set ℝ) : densityAverage T E u omega ≤ ∫ z, topProfile 203 z ∂volume.prod volume := by
  unfold densityAverage
  apply (div_le_iff₀ T.area_pos).mpr
  have h := setIntegral_le_integral (s := E ∩ u ⁻¹' omega)
    (T.densityKernel_integrable (by norm_num : (2:ℝ)<203))
    (Filter.Eventually.of_forall (fun z => T.densityKernel_nonneg 203 z))
  exact h.trans_eq (T.integral_densityKernel 203)

namespace OrdinaryDensityTile

theorem densityValues_nonempty (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    (tile.densityValues ell0 w W tau q E u).Nonempty := ⟨0,Or.inl rfl⟩

theorem density_le (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    tile.density ell0 w W tau q E u ≤ ∫ z, topProfile 203 z ∂volume.prod volume := by
  apply csSup_le (tile.densityValues_nonempty ell0 w W tau q E u)
  intro x hx
  rcases hx with rfl | ⟨test,rfl⟩
  · exact integral_nonneg (topProfile_nonnegative 203)
  · exact densityAverage_le test.top E u _

end OrdinaryDensityTile
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCoefficient
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analyzing coefficients for unrestricted packet lattices and their
exact transport to the local reference lattice. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem physical_multiplier_analyzing_integrable (t : ℝ) (m : ℝ×ℝ → ℂ)
    (hm : Measurable m) (hm1 : ∀ z, ‖m z‖ ≤ 1)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ) :
    Integrable (fun z => g z k*conj (m z*P.physicalPacket t j l u k z))
      (volume.prod volume) := by
  have hgm : Measurable (fun z => g z k) :=
    (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
  apply (P.physicalPacket t j l u k).integrable.norm.mono'
    (hgm.mul (continuous_star.measurable.comp
      (hm.mul (P.physicalPacket t j l u k).continuous.measurable))).aestronglyMeasurable
  filter_upwards [] with z
  change ‖g z k*conj (m z*P.physicalPacket t j l u k z)‖ ≤ ‖P.physicalPacket t j l u k z‖
  rw [norm_mul,Complex.norm_conj,norm_mul]
  have hgk : ‖g z k‖ ≤ 1 := (PiLp.norm_apply_le (g z) k).trans (hg1 z)
  calc
    _ ≤ 1*(1*‖P.physicalPacket t j l u k z‖) := mul_le_mul hgk
      (mul_le_mul_of_nonneg_right (hm1 z) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = _ := by ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceTransverseTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The remaining transverse tail in the long-tree density estimate:
412 powers in squared energy absorb twice the density loss 203, leaving
the summable sixth power. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem transverseTailConstant_nonneg : 0≤transverseTailConstant :=
  tsum_nonneg (fun _ => by positivity)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PacketAngularCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-scale angular cells containing both the packet spectrum and
its selector support. The three nested grids are the existing literal
alternating one-third grids. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketRepresentation

theorem exists_scaled_three_grid_cover (unit : ℝ) (hu : 0<unit)
    (k : ℤ) (c r : ℝ) (hr : 0 ≤ r)
    (hsmall : 6*r<unit*DyadicLineGrid.scale k) :
    ∃ grid∈Finset.Icc (-1) 1, ∃ cell : ℤ,
      Icc (c-r) (c+r) ⊆ scaledAngularCell unit grid k cell := by
  have hs : 6*(r/unit)<DyadicLineGrid.scale k := by
    rw [←mul_div_assoc]
    apply (div_lt_iff₀ hu).2
    simpa only [mul_comm] using hsmall
  obtain ⟨grid,hg,cell,hc⟩ := DyadicLineGrid.exists_three_grid_cover k
    (c/unit) (r/unit) (div_nonneg hr hu.le) hs
  refine ⟨grid,hg,cell,?_⟩
  intro x hx
  apply hc
  constructor
  · have h := (div_le_div_iff_of_pos_right hu).mpr hx.1
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have h := (div_le_div_iff_of_pos_right hu).mpr hx.2
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring

theorem frequency_margin_subset {S : Set ℝ} (l w xi eta theta c C margin : ℝ)
    (hl : 0<l) (hw : 0<w) (hc : 0 < c) (hC : 0≤C) (_hm : 0 ≤ margin)
    (hV : c≤w*eta) (hX : |symbolX l xi eta theta|≤C)
    (hcell : Icc (theta-(C/c+margin)*(w/l))
      (theta+(C/c+margin)*(w/l)) ⊆ S) :
    Icc (-xi/eta-margin*(w/l)) (-xi/eta+margin*(w/l)) ⊆ S := by
  have hs := abs_le.mp (frequency_slope_margin l w xi eta theta c C hl hw hc hC hV hX)
  intro s hs'
  apply hcell
  constructor <;> nlinarith only [hs.1,hs.2,hs'.1,hs'.2]

/-- A single selected angular cell contains the selector support and the
entire spectrum with the requested margin. -/
theorem exists_packet_angular_cell (unit : ℝ) (hu : 0<unit) (k : ℤ)
    (l w theta c C margin radius : ℝ) (hl : 0<l) (hw : 0<w)
    (hc : 0 < c) (hC : 0≤C) (hm : 0 ≤ margin) (hr : 0 ≤ radius)
    (hprecision : w/l=unit*DyadicLineGrid.scale k)
    (hsmall : 6*max radius (C/c+margin)<1) :
    ∃ grid∈Finset.Icc (-1) 1, ∃ cell : ℤ,
      (∀ s, |s-theta| ≤ radius*(w/l) → s∈scaledAngularCell unit grid k cell) ∧
      (∀ xi eta, c≤w*eta → |symbolX l xi eta theta|≤C →
        Icc (-xi/eta-margin*(w/l)) (-xi/eta+margin*(w/l)) ⊆
          scaledAngularCell unit grid k cell) := by
  have hd : 0<w/l := div_pos hw hl
  let R := max radius (C/c+margin)
  have hR : 0≤R := hr.trans (le_max_left _ _)
  obtain ⟨grid,hg,cell,hcell⟩ := exists_scaled_three_grid_cover unit hu k theta
    (R*(w/l)) (mul_nonneg hR hd.le) (by
      rw [←hprecision]
      have h := mul_lt_mul_of_pos_right hsmall hd
      convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring)
  refine ⟨grid,hg,cell,?_,?_⟩
  · intro s hs
    apply hcell
    have hs' := abs_le.mp hs
    have hle := mul_le_mul_of_nonneg_right (le_max_left radius (C/c+margin)) hd.le
    constructor <;> dsimp only [R] at * <;> linarith
  · intro xi eta hV hX
    apply frequency_margin_subset l w xi eta theta c C margin hl hw hc hC hm hV hX
    intro s hs
    apply hcell
    have hle := mul_le_mul_of_nonneg_right (le_max_right radius (C/c+margin)) hd.le
    constructor <;> dsimp only [R] at * <;> linarith only [hs.1,hs.2,hle]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PacketAngularAssignment
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simultaneous choice of one of three angular grids for every
label. Its cells carry both the selector and the spectral margin. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem precision_eq_scaled_grid (w : ℝ) (j : Fin N) :
    w/P.length j = (w/P.topLength)*DyadicLineGrid.scale (j.val:ℤ) := by
  rw [length,DyadicLineGrid.scale,zpow_natCast]
  field_simp [P.topLength_pos.ne',pow_ne_zero _ (by norm_num : (2:ℝ)≠0)]

theorem exists_angular_assignment (w cStar cEta margin radius : ℝ)
    (hw : 0<w) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hm : 0 ≤ margin) (hr : 0 ≤ radius)
    (hsmall : 6*max radius (cStar/cEta+margin)<1) :
    ∃ grid : ∀ j, P.labels j → DyadicLineGrid.GridChoice,
    ∃ cell : ∀ j, P.labels j → ℤ,
      ∀ j (l : P.labels j),
        (∀ s, |s-P.rowSlope j l| ≤ radius*(w/P.length j) →
          s∈scaledAngularCell (w/P.topLength) (grid j l).val j.val (cell j l)) ∧
        (∀ xi eta, cEta≤w*eta →
          |xi+P.rowSlope j l*eta| ≤ cStar/P.length j →
          Icc (-xi/eta-margin*(w/P.length j)) (-xi/eta+margin*(w/P.length j)) ⊆
            scaledAngularCell (w/P.topLength) (grid j l).val j.val (cell j l)) := by
  classical
  have h (j : Fin N) (l : P.labels j) :
      ∃ g : DyadicLineGrid.GridChoice, ∃ cell : ℤ,
        (∀ s, |s-P.rowSlope j l| ≤ radius*(w/P.length j) →
          s∈scaledAngularCell (w/P.topLength) g.val j.val cell) ∧
        (∀ xi eta, cEta≤w*eta →
          |xi+P.rowSlope j l*eta| ≤ cStar/P.length j →
          Icc (-xi/eta-margin*(w/P.length j)) (-xi/eta+margin*(w/P.length j)) ⊆
            scaledAngularCell (w/P.topLength) g.val j.val cell) := by
    obtain ⟨g,hg,cell,hsel,hspec⟩ := PacketRepresentation.exists_packet_angular_cell
      (w/P.topLength) (div_pos hw P.topLength_pos) j.val
      (P.length j) w (P.rowSlope j l) cEta cStar margin radius
      (P.length_pos j) hw hcEta hcStar hm hr (P.precision_eq_scaled_grid w j) hsmall
    refine ⟨⟨g,hg⟩,cell,hsel,?_⟩
    intro xi eta hV hX
    apply hspec xi eta hV
    rw [PacketRepresentation.symbolX,abs_mul,abs_of_pos (P.length_pos j)]
    have hh := (le_div_iff₀ (P.length_pos j)).mp hX
    simpa only [mul_comm] using hh
  choose grid cell hcell using h
  exact ⟨grid,cell,hcell⟩

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedSum
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact synthesis and separated-energy identities for the selected
reference lattice, with its cost expressed only in the original fixed
profile bounds. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem referenceEnvelopeConstant_pos :
    0<P.referenceEnvelopeConstant := by
  have hp := P.profileBound_pos
  have hr : 0<P.ratioBound := zero_lt_one.trans_le P.ratioBound_ge_one
  unfold referenceEnvelopeConstant
  positivity

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataModelConfig
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed geometric and selector data for the ordinary model. None of
these parameters depends on the input function or the tested set. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

namespace OrdinaryModelConfig
variable {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

theorem sizeAreaConstant_nonneg (d : OrdinaryModelConfig P initial) (CS : ℝ) :
    0≤d.sizeAreaConstant CS := by
  dsimp [sizeAreaConstant,selectedNearConstant]
  positivity

end OrdinaryModelConfig
end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceThresholdSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform summation over any finite family of dyadic density thresholds. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem ordinaryThresholdRatio_lt_one : ordinaryThresholdRatio<1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAdjoint
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal finite adjoint duality for the ordinary masked packets. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem masked_physical_packet_memLp
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (q : P.PacketIndex) (k : κ) :
    MemLp (fun z => b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      2 (volume.prod volume) := by
  apply ((P.physicalPacket 0 q.1 q.2.1 q.2.2 k).memLp 2 (volume.prod volume)).mono
    ((((hb q.1 q.2.1 k).comp hu).mul
      (P.physicalPacket 0 q.1 q.2.1 q.2.2 k).continuous.measurable).aestronglyMeasurable)
  filter_upwards [] with z
  change ‖b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z‖≤_
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb1 q.1 q.2.1 k (u z))

theorem ordinaryAdjointSum_memLp (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    MemLp (P.ordinaryAdjointSum S b u g) 2 (volume.prod volume) :=
  memLp_finsetSum S (fun q _ => P.packetVector_memLp _ q)

theorem ordinary_forward_pairing (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : MemLp g 2 (volume.prod volume)) :
    (∫ z, inner ℂ (P.ordinaryForwardSum S b u f z) (g z) ∂volume.prod volume)=
      ∑ q∈S, ((P.length q.1*P.width:ℝ):ℂ)*inner ℂ
        (P.ordinaryCoefficient f q.1 q.2.1 q.2.2)
        (P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2) := by
  let area := fun q : P.PacketIndex => P.length q.1*P.width
  let masked := fun (q : P.PacketIndex) (k : κ) (z : ℝ×ℝ) =>
    b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z
  let cf := fun q : P.PacketIndex => P.ordinaryCoefficient f q.1 q.2.1 q.2.2
  have ha (q : P.PacketIndex) (_hq : q∈S) : area q≠0 := (mul_pos (P.length_pos _) P.width_pos).ne'
  have hm (q : P.PacketIndex) (_hq : q∈S) (k : κ) :
      Integrable (fun z => g z k*conj (masked q k z)) (volume.prod volume) :=
    ((memLp_piLp_iff.mp hg) k).integrable_mul (P.masked_physical_packet_memLp b hb hb1 u hu q k).star
  have h := finite_analyzing_pairing (volume.prod volume) area masked g cf S ha hm
  have he (z : ℝ×ℝ) : (∑ q∈S, WithLp.toLp 2 (fun k => cf q k*masked q k z))=
      P.ordinaryForwardSum S b u f z := by
    apply Finset.sum_congr rfl
    intro q _
    apply WithLp.ofLp_injective
    funext k
    change cf q k*(b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)=
      cf q k*b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z
    ring
  have hc (q : P.PacketIndex) : analyzingCoefficient (volume.prod volume) area masked g q=
      P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 := rfl
  simp_rw [he,hc] at h
  exact h

theorem ordinary_adjoint_pairing (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ) (hf : MemLp f 2 (volume.prod volume)) :
    (∫ z, inner ℂ (P.ordinaryAdjointSum S b u g z) (f z) ∂volume.prod volume)=
      ∑ q∈S, ((P.length q.1*P.width:ℝ):ℂ)*inner ℂ
        (P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2)
        (P.ordinaryCoefficient f q.1 q.2.1 q.2.2) := by
  apply finite_analyzing_pairing (volume.prod volume)
    (fun q : P.PacketIndex => P.length q.1*P.width)
    (fun q k => P.physicalPacket 0 q.1 q.2.1 q.2.2 k) f
    (fun q => P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2) S
  · intro q _
    exact (mul_pos (P.length_pos _) P.width_pos).ne'
  · intro q _ k
    exact ((memLp_piLp_iff.mp hf) k).integrable_mul
      ((P.physicalPacket 0 q.1 q.2.1 q.2.2 k).memLp 2 (volume.prod volume)).star

theorem ordinary_forward_adjoint_pairing (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : MemLp f 2 (volume.prod volume)) (hg : MemLp g 2 (volume.prod volume)) :
    (∫ z, inner ℂ (P.ordinaryForwardSum S b u f z) (g z) ∂volume.prod volume)=
      conj (∫ z, inner ℂ (P.ordinaryAdjointSum S b u g z) (f z) ∂volume.prod volume) := by
  rw [P.ordinary_forward_pairing S b hb hb1 u hu f g hg,P.ordinary_adjoint_pairing S b u f g hf,map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_mul,Complex.conj_ofReal,inner_conj_symm]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCrossValue
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual distinct-profile, masked analyzing packet sum. No auxiliary
jet is needed for the physical bilinear operator. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)

theorem crossPacketValue_memLp (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (p : ℝ≥0∞) (q : P.PacketIndex) :
    MemLp (fun z => P.crossPacketValue alt hAlt t b v g z q) p (volume.prod volume) := by
  apply memLp_piLp_iff.mpr
  intro k
  exact (((P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k).memLp p
    (volume.prod volume)).const_mul _

theorem crossSum_memLp (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (p : ℝ≥0∞) (S : Finset P.PacketIndex) :
    MemLp (fun z => ∑ q∈S, P.crossPacketValue alt hAlt t b v g z q) p (volume.prod volume) :=
  memLp_finsetSum S (fun q _ => P.crossPacketValue_memLp alt hAlt t b v g p q)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCrossForm
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical distinct-profile sum is exactly the finite coefficient
form used in the packet representation. Both sides keep the original
spatial sites and analyzing coefficients. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem cross_coefficient_form (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (S : Finset P.PacketIndex) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (u : ℝ×ℝ → ℝ) (g f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : MemLp f 2 (volume.prod volume)) :
    (∫ z, inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q) (f z)
      ∂volume.prod volume) =
      ∑ q∈S, ((P.length q.1*P.width:ℝ):ℂ)*inner ℂ
        (P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2)
        ((P.withProfile alt hAlt).ordinaryCoefficient f q.1 q.2.1 q.2.2) := by
  apply finite_analyzing_pairing (volume.prod volume)
    (fun q : P.PacketIndex => P.length q.1*P.width)
    (fun q k => (P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) f
    (fun q => P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2) S
  · intro q _
    exact (mul_pos (P.length_pos _) P.width_pos).ne'
  · intro q _ k
    exact ((memLp_piLp_iff.mp hf) k).integrable_mul
      (((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k).memLp 2
        (volume.prod volume)).star

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCrossProductForm
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Expansion into the two literal wave integrals. This is the finite
form to which the translated convolution packet identity applies. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem cross_product_form (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (S : Finset P.PacketIndex) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (u : ℝ×ℝ → ℝ) (g f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : MemLp f 2 (volume.prod volume)) :
    (∫ z, inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q) (f z)
      ∂volume.prod volume) =
      ∑ q∈S, ∑ k, ((P.length q.1*P.width:ℝ):ℂ)⁻¹*
        (∫ z, f z k*conj ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k z)
          ∂volume.prod volume)*
        (∫ z, b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z*conj (g z k)
          ∂volume.prod volume) := by
  rw [P.cross_coefficient_form alt hAlt S b u g f hf]
  apply Finset.sum_congr rfl
  intro q _
  simp only [PiLp.inner_apply,RCLike.inner_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hc : conj (∫ z, g z k*conj (b q.1 q.2.1 k (u z)*
      P.physicalPacket 0 q.1 q.2.1 q.2.2 k z) ∂volume.prod volume) =
      ∫ z, b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z*conj (g z k)
        ∂volume.prod volume := by
    rw [←integral_conj]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [map_mul,starRingEnd_self_apply]
    ring
  simp only [ordinaryCoefficient,physicalMultiplierCoefficient,analyzingCoefficient,
    WithLp.ofLp_toLp]
  have hlen : (P.withProfile alt hAlt).length q.1 = P.length q.1 := rfl
  have hwidth : (P.withProfile alt hAlt).width = P.width := rfl
  simp only [hlen,hwidth]
  rw [map_mul,map_inv₀,Complex.conj_ofReal,hc]
  have ha : (↑(P.length q.1*P.width):ℂ)≠0 := by
    exact_mod_cast (mul_pos (P.length_pos q.1) P.width_pos).ne'
  field_simp

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataKernelForm
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact passage from a physical coefficient form to the finite sum
of convolution packet products, retaining the inverse-area factor. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
open PacketRepresentation

theorem cross_kernel_form (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (S : Finset P.PacketIndex) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (u : ℝ×ℝ → ℝ) (g f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : MemLp f 2 (volume.prod volume))
    (KA KB : P.PacketIndex → κ → (ℝ×ℝ) → ℂ)
    (site : P.PacketIndex → ℝ×ℝ)
    (hA : ∀ q∈S, ∀ k x, P.physicalPacket 0 q.1 q.2.1 q.2.2 k x =
      synthesisWave (P.length q.1*P.width) (KA q k) (site q) x)
    (hB : ∀ q∈S, ∀ k x, (P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k x =
      analyzingWave (P.length q.1*P.width) (KB q k) (site q) x) :
    (∫ z, inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q) (f z)
      ∂volume.prod volume) =
      ∑ q∈S, ∑ k, ((P.length q.1*P.width:ℝ):ℂ)⁻¹*
        packetProduct (KA q k) (KB q k) (fun z => f z k)
          (fun z => b q.1 q.2.1 k (u z)) (fun z => g z k)
          (P.length q.1*P.width) (site q) := by
  rw [P.cross_product_form alt hAlt S b u g f hf]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [hA q hq k, hB q hq k]
  rw [packetProduct,coefficient]
  ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_NormalizedPacketKernelForm
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized Fourier kernels realize the finite physical
coefficient form, including every carrier and the exact area factors. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
  (topLength width scale ratioBound C : ℝ) (order : ℕ)
  (htop : 0<topLength) (hwidth : 0<width) (hC : 0<C) (horder : 3≤order)
  (hratio : 1 ≤ ratioBound) (hscale : |scale/width| ≤ ratioBound)
  (labels : ∀ j, Finset (Label j))
  (originX originZ theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
  (site : ∀ j (l : labels j), Item j l → ℤ×ℤ)
  (hinj : ∀ j l, Function.Injective (site j l))
  (hprofile : planarProfileConstant (synthesisProfile F q nu) (2*order) ≤ C)

local notation "P" => normalizedPacketLattice F q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile

variable (G : SchwartzMap (ℝ×ℝ) ℂ)
  (hG : planarProfileConstant (analysisProfile G q nu) (2*order)≤C)

local notation "alt" => normalizedAnalysisFamily F q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile G
local notation "hAlt" => normalizedAnalysisFamily_bound F q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile G hG

theorem normalized_packet_kernel_form
    (S : Finset (P).PacketIndex) (b : ∀ j, (P).labels j → κ → ℝ → ℂ)
    (u : ℝ×ℝ → ℝ) (g f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : MemLp f 2 (volume.prod volume)) :
    let KA := fun (s : (P).PacketIndex) (k : κ) => horizontalFrequencyKernel
      (scaledFrequencyWindow F ((P).length s.1) width (theta s.1 s.2.1)
        (2*Real.pi*center k) ((P).length_pos s.1).ne' hwidth.ne')
      nu q ((P).length s.1) (theta s.1 s.2.1)
    let KB := fun (s : (P).PacketIndex) (k : κ) => verticalFrequencyKernel
      (scaledFrequencyWindow G ((P).length s.1) width (theta s.1 s.2.1)
        (2*Real.pi*center k) ((P).length_pos s.1).ne' hwidth.ne')
      nu q width (center k)
    (∫ z, inner ℂ (∑ s∈S, (P).crossPacketValue alt hAlt 0 b u g z s) (f z)
      ∂volume.prod volume) =
      ∑ s∈S, ∑ k, (((P).length s.1*width:ℝ):ℂ)⁻¹*
        packetProduct (KA s k) (KB s k) (fun z => f z k)
          (fun z => b s.1 s.2.1 k (u z)) (fun z => g z k)
          ((P).length s.1*width) ((P).actualX s.1 s.2.1 s.2.2,(P).actualZ s.1 s.2.1 s.2.2) := by
  intro KA KB
  apply (P).cross_kernel_form alt hAlt S b u g f hf (fun s k x => KA s k x) (fun s k x => KB s k x)
    (fun s => ((P).actualX s.1 s.2.1 s.2.2,(P).actualZ s.1 s.2.1 s.2.2))
  · intro s _ k x
    exact normalizedPacketLattice_synthesis F q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile s.1 s.2.1 s.2.2 k x
  · intro s _ k x
    have h := normalizedAnalysisFamily_packet F q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile G s.1 s.2.1 s.2.2 k x
    change physicalPlanarPacket (alt s.1 s.2.1 s.2.2 k)
      ((P).actualX s.1 s.2.1 s.2.2)
      ((P).actualZ s.1 s.2.1 s.2.2+0*(P).actualX s.1 s.2.1 s.2.2)
      ((P).length s.1) width (0+theta s.1 s.2.1) (2*Real.pi*center k)
      _ _ x = analyzingWave ((P).length s.1*width) (KB s k)
        ((P).actualX s.1 s.2.1 s.2.2,(P).actualZ s.1 s.2.1 s.2.2) x
    simpa only [KB,zero_mul,add_zero,zero_add] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataLatticeSites
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical sites are exactly the translated sheared lattices used
by the common probability average. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem actualSite_eq_lattice_translate (P : PacketLatticeData N κ Label Item)
    (j : Fin N) (l : P.labels j) (a : Item j l) :
    (P.actualX j l a,P.actualZ j l a) =
      PacketRepresentation.latticeHom (P.length j) P.width (P.rowSlope j l) (P.site j l a)+
        (P.originX j l,P.originZ j l) := by
  apply Prod.ext <;>
    simp only [actualX,actualZ,PacketRepresentation.latticeHom,AddMonoidHom.coe_mk,
      ZeroHom.coe_mk,Prod.fst_add,Prod.snd_add] <;> ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_FiniteNormalizedPacketLattice
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Realization of an arbitrary finite part of the translated lattice
by the actual normalized packet data. The site fibers are shared by
all carrier components and add no extra terms. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]
variable (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
  (topLength width scale ratioBound C : ℝ) (order : ℕ)
  (htop : 0<topLength) (hwidth : 0<width) (hC : 0<C) (horder : 3≤order)
  (hratio : 1 ≤ ratioBound) (hscale : |scale/width| ≤ ratioBound)
  (labels : ∀ j, Finset (Label j))
  (origin : ∀ j, labels j → ℝ×ℝ) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
  (S : Finset (LatticeSiteIndex labels))
  (hprofile : planarProfileConstant (synthesisProfile F q nu) (2*order)≤C)

attribute [local instance] Classical.propDecidable

local notation "P" => finiteNormalizedPacketLattice F q nu topLength width scale ratioBound C order
  htop hwidth hC horder hratio hscale labels origin theta center S hprofile

theorem finiteNormalizedPacket_sum {E : Type*} [AddCommMonoid E]
    (f : LatticeSiteIndex labels → E) :
    (∑ s : (P).PacketIndex, f ⟨s.1,⟨s.2.1,s.2.2.val⟩⟩) = ∑ s∈S, f s := by
  have h := Equiv.sum_comp
    (finiteNormalizedPacketEquiv F q nu topLength width scale ratioBound C order
      htop hwidth hC horder hratio hscale labels origin theta center S hprofile)
    (fun s : S => f s.val)
  exact h.trans (Finset.sum_subtype S (p := fun s => s∈S) (by simp) f).symm

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteNormalizedKernelForm
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite convolution form is realized on the arbitrary
retained subset of the common translated spatial lattices. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]
variable (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
  (topLength width scale ratioBound C : ℝ) (order : ℕ)
  (htop : 0<topLength) (hwidth : 0<width) (hC : 0<C) (horder : 3≤order)
  (hratio : 1 ≤ ratioBound) (hscale : |scale/width| ≤ ratioBound)
  (labels : ∀ j, Finset (Label j))
  (origin : ∀ j, labels j → ℝ×ℝ) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
  (S : Finset (LatticeSiteIndex labels))
  (hprofile : planarProfileConstant (synthesisProfile F q nu) (2*order)≤C)


local notation "P" => finiteNormalizedPacketLattice F q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels origin theta center S hprofile

variable (G : SchwartzMap (ℝ×ℝ) ℂ)
  (hG : planarProfileConstant (analysisProfile G q nu) (2*order)≤C)

theorem finite_normalized_kernel_form
    (b : ∀ j, (P).labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (g f : ℝ×ℝ → EuclideanSpace ℂ κ) (hf : MemLp f 2 (volume.prod volume)) :
    let alt := fun (j : Fin N) (l : (P).labels j)
      (_a : finiteSiteFiber labels S j l.val) (_k : κ) => analysisProfile G q nu
    let hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*(P).order)≤(P).profileBound :=
      fun _ _ _ _ => hG
    let KA := fun (s : LatticeSiteIndex labels) (k : κ) => horizontalFrequencyKernel
      (scaledFrequencyWindow F ((P).length s.1) width (theta s.1 s.2.1)
        (2*Real.pi*center k) ((P).length_pos s.1).ne' hwidth.ne')
      nu q ((P).length s.1) (theta s.1 s.2.1)
    let KB := fun (s : LatticeSiteIndex labels) (k : κ) => verticalFrequencyKernel
      (scaledFrequencyWindow G ((P).length s.1) width (theta s.1 s.2.1)
        (2*Real.pi*center k) ((P).length_pos s.1).ne' hwidth.ne')
      nu q width (center k)
    (∫ z, inner ℂ (∑ a : (P).PacketIndex,
      (P).crossPacketValue alt hAlt 0 b u g z a) (f z) ∂volume.prod volume) =
    ∑ s∈S, ∑ k, (((P).length s.1*width:ℝ):ℂ)⁻¹*
      packetProduct (KA s k) (KB s k) (fun z => f z k)
        (fun z => b s.1 s.2.1 k (u z)) (fun z => g z k) ((P).length s.1*width)
        (latticeHom ((P).length s.1) width (theta s.1 s.2.1) s.2.2+origin s.1 s.2.1) := by
  intro alt hAlt KA KB
  have hrep := normalized_packet_kernel_form
    (Item := fun j l => finiteSiteFiber labels S j l)
    F q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale
    labels (fun j l => (origin j l).1) (fun j l => (origin j l).2) theta center
    (fun _ _ n => n.val) (fun _ _ => Subtype.val_injective) hprofile G hG
    (Finset.univ : Finset (P).PacketIndex) b u g f hf
  dsimp only at hrep
  simp_rw [PacketLatticeData.actualSite_eq_lattice_translate] at hrep
  have hsum := finiteNormalizedPacket_sum F q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels origin theta center S hprofile
    (fun s => ∑ k, (((P).length s.1*width:ℝ):ℂ)⁻¹*
      packetProduct (KA s k) (KB s k) (fun z => f z k)
        (fun z => b s.1 s.2.1 k (u z)) (fun z => g z k) ((P).length s.1*width)
        (latticeHom ((P).length s.1) width (theta s.1 s.2.1) s.2.2+origin s.1 s.2.1))
  exact hrep.trans hsum

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_JointVectorPacketAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All carrier components share the same site at each scale and direction.
Averaging preserves the vector packet estimate without a dimension factor. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem joint_vector_convolution_packet_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (KA KB f b g : ι → κ → (ℝ×ℝ) → ℂ)
    (hA : ∀ i k, Integrable (KA i k) planeMeasure)
    (hB : ∀ i k, Integrable (KB i k) planeMeasure)
    (hf : ∀ i k, Integrable (f i k) planeMeasure)
    (hb : ∀ i k, Measurable (b i k)) (hg : ∀ i k, Measurable (g i k))
    (Mb Mg : ι → κ → ℝ)
    (hbb : ∀ i k x, ‖b i k x‖≤Mb i k) (hgb : ∀ i k x, ‖g i k x‖≤Mg i k)
    (l W theta : ι → ℝ) (hl : ∀ i, 0<l i) (hW : ∀ i, 0<W i)
    (C : ℝ)
    (hfinite : ∀ z : ι → (ℝ×ℝ), ∀ S : Finset (ι×(ℤ×ℤ)),
      ‖∑ p ∈ S, ∑ k, ((l p.1*W p.1:ℝ):ℂ)⁻¹*
        packetProduct (KA p.1 k) (KB p.1 k) (f p.1 k) (b p.1 k) (g p.1 k)
          (l p.1*W p.1) (latticeHom (l p.1) (W p.1) (theta p.1) p.2+z p.1)‖≤C) :
    ‖∑ i, ∑ k, ∫ x, b i k x*
      kernelConvolution (KA i k) (kernelConvolution (KB i k) (f i k)) x*
      conj (g i k x) ∂planeMeasure‖≤C := by
  let F := fun i z => ∑ k, packetProduct (KA i k) (KB i k) (f i k) (b i k) (g i k)
    (l i*W i) z
  have hprod (i : ι) (k : κ) :
      Integrable (packetProduct (KA i k) (KB i k) (f i k) (b i k) (g i k) (l i*W i))
        planeMeasure :=
    packetProduct_integrable (KA i k) (KB i k) (f i k) (b i k) (g i k)
      (hA i k) (hB i k) (hf i k) (hb i k) (hg i k)
      (Mb i k) (Mg i k) (hbb i k) (hgb i k) (l i*W i)
  have hF (i : ι) : Integrable (F i) planeMeasure :=
    integrable_finsetSum _ (fun k _ => hprod i k)
  have h := joint_lattice_average_bound l W theta hl hW F hF C (by
    intro z S
    simpa only [F,Finset.mul_sum] using hfinite z S)
  have heq (i : ι) : (∑ k, ∫ x, b i k x*
      kernelConvolution (KA i k) (kernelConvolution (KB i k) (f i k)) x*
      conj (g i k x) ∂planeMeasure) =
      (((l i*W i:ℝ):ℂ)^2)⁻¹*∫ z, F i z ∂planeMeasure := by
    simp only [F]
    rw [integral_finsetSum _ (fun k _ => hprod i k),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact continuous_packet_identity (KA i k) (KB i k) (f i k) (b i k) (g i k)
      (hA i k) (hB i k) (hf i k) (hb i k) (hg i k)
      (Mb i k) (Mg i k) (hbb i k) (hgb i k) (l i*W i) (mul_pos (hl i) (hW i)).ne'
  simpa only [heq] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NormalizedLatticeAverage
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete finite scale/direction convolution sum follows from
the bounds on its actual normalized finite packet models. Every carrier
shares each spatial lattice, before taking the probability average. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]

theorem normalized_lattice_average_bound
    (F G : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
    (topLength width scale ratioBound C : ℝ) (order : ℕ)
    (htop : 0<topLength) (hwidth : 0<width) (hC : 0<C) (horder : 3≤order)
    (hratio : 1 ≤ ratioBound) (hscale : |scale/width| ≤ ratioBound)
    (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (hprofile : planarProfileConstant (synthesisProfile F q nu) (2*order)≤C)
    (hG : planarProfileConstant (analysisProfile G q nu) (2*order)≤C)
    (b : ∀ j, labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : MemLp f 2 (volume.prod volume))
    (hf1 : ∀ k, Integrable (fun z => f z k) (volume.prod volume))
    (hg : ∀ k, Measurable (fun z => g z k)) (hg1 : ∀ k z, ‖g z k‖≤1)
    (B : ℝ)
    (hFinite : ∀ (origin : ∀ j, labels j → ℝ×ℝ) (S : Finset (LatticeSiteIndex labels)),
      let P := finiteNormalizedPacketLattice F q nu topLength width scale ratioBound C order
        htop hwidth hC horder hratio hscale labels origin theta center S hprofile
      let alt := fun (j : Fin N) (l : P.labels j)
        (_a : finiteSiteFiber labels S j l.val) (_k : κ) => analysisProfile G q nu
      let hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound :=
        fun _ _ _ _ => hG
      ‖∫ z, inner ℂ (∑ a : P.PacketIndex,
        P.crossPacketValue alt hAlt 0 b u g z a) (f z) ∂volume.prod volume‖≤B) :
    let length := fun i : LatticeRow labels => topLength/(2:ℝ)^i.1.val
    let KA := fun (i : LatticeRow labels) (k : κ) => horizontalFrequencyKernel
      (scaledFrequencyWindow F (length i) width (theta i.1 i.2) (2*Real.pi*center k)
        (div_pos htop (pow_pos (by norm_num) _)).ne' hwidth.ne') nu q (length i) (theta i.1 i.2)
    let KB := fun (i : LatticeRow labels) (k : κ) => verticalFrequencyKernel
      (scaledFrequencyWindow G (length i) width (theta i.1 i.2) (2*Real.pi*center k)
        (div_pos htop (pow_pos (by norm_num) _)).ne' hwidth.ne') nu q width (center k)
    ‖∑ i : LatticeRow labels, ∑ k, ∫ x, b i.1 i.2 k (u x)*
      kernelConvolution (KA i k) (kernelConvolution (KB i k) (fun z => f z k)) x*
      star (g x k) ∂volume.prod volume‖≤B := by
  intro length KA KB
  apply joint_vector_convolution_packet_bound
    (fun i k z => KA i k z) (fun i k z => KB i k z)
    (fun _ k z => f z k) (fun i k z => b i.1 i.2 k (u z)) (fun _ k z => g z k)
    (fun i k => (KA i k).integrable) (fun i k => (KB i k).integrable)
    (fun _ k => hf1 k) (fun i k => (hb i.1 i.2 k).comp hu) (fun _ k => hg k)
    (fun _ _ => 1) (fun _ _ => 1) (fun i k z => hb1 i.1 i.2 k (u z))
    (fun _ k z => hg1 k z) length (fun _ => width) (fun i => theta i.1 i.2)
    (fun i => div_pos htop (pow_pos (by norm_num) i.1.val)) (fun _ => hwidth) B
  intro origin S
  let R := S.map (latticeSiteProductEquiv labels).symm.toEmbedding
  let O := fun j l => origin (⟨j,l⟩ : LatticeRow labels)
  have hm := hFinite O R
  have heq := finite_normalized_kernel_form F q nu topLength width scale ratioBound C order
    htop hwidth hC horder hratio hscale labels O theta center R hprofile G hG b u g f hf
  dsimp only at hm heq
  rw [heq] at hm
  dsimp only [R] at hm
  rw [sum_joint_lattice_sites] at hm
  exact hm

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ScaledWindowFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Fourier coordinates of the normalized physical kernels.
The Jacobian is derived by two one-dimensional changes of variables. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem integral_packetCoordinates (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta : ℝ) (hl : l≠0) (hW : W≠0) :
    (∫ z, F (packetCoordinates l W theta hl hW z) ∂planeMeasure)=
      |l*W| • (∫ z, F z ∂planeMeasure) := by
  let G := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (packetCoordinates l W theta hl hW) F
  have hi : Integrable (fun z => F (packetCoordinates l W theta hl hW z)) planeMeasure := G.integrable
  have hs (x : ℝ) : (∫ y : ℝ, F (x/l,(y-theta*x)/W))=
      |W| • (∫ y : ℝ, F (x/l,y)) := by
    rw [integral_sub_right_eq_self (fun y : ℝ => F (x/l,y/W)) (theta*x)]
    exact Measure.integral_comp_div (fun y : ℝ => F (x/l,y)) W
  calc
    _ = ∫ x : ℝ, ∫ y : ℝ, F (x/l,(y-theta*x)/W) := integral_prod _ hi
    _ = ∫ x : ℝ, |W| • (∫ y : ℝ, F (x/l,y)) :=
      integral_congr_ae (Filter.Eventually.of_forall hs)
    _ = |W| • (∫ x : ℝ, ∫ y : ℝ, F (x/l,y)) := integral_smul _ _
    _ = |W| • (|l| • (∫ x : ℝ, ∫ y : ℝ, F (x,y))) := by
      rw [Measure.integral_comp_div (fun x : ℝ => ∫ y : ℝ, F (x,y)) l]
    _ = _ := by
      rw [smul_smul, ← integral_prod _ F.integrable, abs_mul, mul_comm]

theorem normalizedSpatialKernel_fourier (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta center : ℝ) (hl : 0<l) (hW : 0<W) (xi eta : ℝ) :
    planarFourier (normalizedSpatialKernel F l W theta (2*Real.pi*center) hl.ne' hW.ne') (xi,eta)=
      planarFourier F (symbolX l xi eta theta,symbolY W eta center) := by
  let X := symbolX l xi eta theta
  let Y := symbolY W eta center
  let G := modulatedFrequencyWindow F (-X) (-Y) 0
  have hpoint (z : ℝ×ℝ) :
      Real.fourierChar (-(z.1*xi+z.2*eta)) •
        normalizedSpatialKernel F l W theta (2*Real.pi*center) hl.ne' hW.ne' z=
      (l*W:ℂ)⁻¹*G (packetCoordinates l W theta hl.ne' hW.ne' z) := by
    simp only [normalizedSpatialKernel, smul_apply, smul_eq_mul, physicalPlanarPacket_apply,
      sub_zero, G, modulatedFrequencyWindow_apply]
    change (Real.fourierChar (-(z.1*xi+z.2*eta)):ℂ)*
      ((l*W:ℂ)⁻¹*(Complex.exp (((2*Real.pi*center)*(z.2-theta*z.1):ℝ)*Complex.I)*
        F (z.1/l,(z.2-theta*z.1)/W)))=
      (l*W:ℂ)⁻¹*((Real.fourierChar ((-X)*(z.1/l)+(-Y)*((z.2-theta*z.1)/W)+0):ℂ)*
        F (z.1/l,(z.2-theta*z.1)/W))
    have hp : (Real.fourierChar (-(z.1*xi+z.2*eta)):ℂ)*
        Complex.exp (((2*Real.pi*center)*(z.2-theta*z.1):ℝ)*Complex.I)=
        (Real.fourierChar ((-X)*(z.1/l)+(-Y)*((z.2-theta*z.1)/W)+0):ℂ) := by
      rw [Real.fourierChar_apply, Real.fourierChar_apply, ← Complex.exp_add]
      congr 1
      dsimp [X,Y,symbolX,symbolY]
      push_cast
      field_simp [show (l:ℂ)≠0 by exact_mod_cast hl.ne', show (W:ℂ)≠0 by exact_mod_cast hW.ne']
      ring
    calc
      _ = (l*W:ℂ)⁻¹*((Real.fourierChar (-(z.1*xi+z.2*eta)):ℂ)*
          Complex.exp (((2*Real.pi*center)*(z.2-theta*z.1):ℝ)*Complex.I))*
            F (z.1/l,(z.2-theta*z.1)/W) := by ring
      _ = _ := by rw [hp]; ring
  have hint : (∫ z, G z ∂planeMeasure)=planarFourier F (X,Y) := by
    unfold planarFourier
    apply integral_congr_ae
    filter_upwards [] with z
    rw [modulatedFrequencyWindow_apply]
    change (Real.fourierChar ((-X)*z.1+(-Y)*z.2+0):ℂ)*F z=
      (Real.fourierChar (-(z.1*X+z.2*Y)):ℂ)*F z
    have he : (-X)*z.1+(-Y)*z.2+0= -(z.1*X+z.2*Y) := by ring
    rw [he]
  unfold planarFourier
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_const_mul,
    integral_packetCoordinates G l W theta hl.ne' hW.ne', abs_of_pos (mul_pos hl hW)]
  rw [Complex.real_smul, ← mul_assoc, Complex.ofReal_mul,
    inv_mul_cancel₀ (show (l:ℂ)*(W:ℂ)≠0 by exact_mod_cast (mul_pos hl hW).ne'), one_mul]
  exact hint

theorem scaledFrequencyWindow_apply (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta center : ℝ) (hl : 0<l) (hW : 0<W) (xi eta : ℝ) :
    scaledFrequencyWindow F l W theta (2*Real.pi*center) hl.ne' hW.ne' (xi,eta)=
      planarFourier F (symbolX l xi eta theta,symbolY W eta center) := by
  rw [scaledFrequencyWindow, planarFourierSchwartz_apply]
  exact normalizedSpatialKernel_fourier F l W theta center hl hW xi eta

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ScaledWindowSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed frequency plateaus give the original narrow spectra for
both actual packet kernels, uniformly in their Fourier-series parameter. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem scaledWindow_inverse_profile_apply (chi : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta center : ℝ) (hl : 0<l) (hW : 0<W) (xi eta : ℝ) :
    scaledFrequencyWindow (planarInverseSchwartz chi) l W theta (2*Real.pi*center)
      hl.ne' hW.ne' (xi,eta)=chi (symbolX l xi eta theta,symbolY W eta center) := by
  rw [scaledFrequencyWindow_apply _ l W theta center hl hW, planarInverseSchwartz_fourier]

theorem horizontalFrequencyKernel_zero_of_window_zero (A : SchwartzMap (ℝ×ℝ) ℂ)
    (nu : SymbolSpace) (q : ℕ) (l theta : ℝ) (omega : ℝ×ℝ) (hz : A omega=0) :
    planarFourier (horizontalFrequencyKernel A nu q l theta) omega=0 := by
  rw [horizontalFrequencyKernel, planarInverseSchwartz_fourier]
  simp only [smul_apply, smul_eq_mul, modulatedFrequencyWindow_apply, hz, mul_zero]

theorem verticalFrequencyKernel_zero_of_window_zero (B : SchwartzMap (ℝ×ℝ) ℂ)
    (nu : SymbolSpace) (q : ℕ) (W center : ℝ) (omega : ℝ×ℝ) (hz : B omega=0) :
    planarFourier (verticalFrequencyKernel B nu q W center) omega=0 := by
  rw [verticalFrequencyKernel, planarInverseSchwartz_fourier]
  simp only [smul_apply, smul_eq_mul, modulatedFrequencyWindow_apply, hz, mul_zero]

theorem scaledWindow_support (chi : SchwartzMap (ℝ×ℝ) ℂ) (A B : ℝ)
    (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (l W theta center : ℝ) (hl : 0<l) (hW : 0<W) (xi eta : ℝ)
    (h : scaledFrequencyWindow (planarInverseSchwartz chi) l W theta (2*Real.pi*center)
      hl.ne' hW.ne' (xi,eta)≠0) :
    |xi+theta*eta|≤A/l ∧ |eta-center|≤B/W := by
  rw [scaledWindow_inverse_profile_apply _ l W theta center hl hW] at h
  have hh := hchi _ h
  constructor
  · apply (le_div_iff₀ hl).2
    simpa only [symbolX, abs_mul, abs_of_pos hl, mul_comm] using hh.1
  · apply (le_div_iff₀ hW).2
    simpa only [symbolY, abs_mul, abs_of_pos hW, mul_comm] using hh.2

theorem horizontal_scaled_kernel_support (chi : SchwartzMap (ℝ×ℝ) ℂ) (A B : ℝ)
    (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (nu : SymbolSpace) (q : ℕ) (l W theta center : ℝ) (hl : 0<l) (hW : 0<W) (xi eta : ℝ)
    (h : planarFourier (horizontalFrequencyKernel
      (scaledFrequencyWindow (planarInverseSchwartz chi) l W theta (2*Real.pi*center) hl.ne' hW.ne')
        nu q l theta) (xi,eta)≠0) :
    |xi+theta*eta|≤A/l ∧ |eta-center|≤B/W := by
  apply scaledWindow_support chi A B hchi l W theta center hl hW xi eta
  intro hz
  exact h (horizontalFrequencyKernel_zero_of_window_zero _ nu q l theta (xi,eta) hz)

theorem vertical_scaled_kernel_support (chi : SchwartzMap (ℝ×ℝ) ℂ) (A B : ℝ)
    (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (nu : SymbolSpace) (q : ℕ) (l W theta center : ℝ) (hl : 0<l) (hW : 0<W) (xi eta : ℝ)
    (h : planarFourier (verticalFrequencyKernel
      (scaledFrequencyWindow (planarInverseSchwartz chi) l W theta (2*Real.pi*center) hl.ne' hW.ne')
        nu q W center) (xi,eta)≠0) :
    |xi+theta*eta|≤A/l ∧ |eta-center|≤B/W := by
  apply scaledWindow_support chi A B hchi l W theta center hl hW xi eta
  intro hz
  exact h (verticalFrequencyKernel_zero_of_window_zero _ nu q W center (xi,eta) hz)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_NormalizedPacketSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact angular-frequency strips for the constructed packet profiles.
Both waves keep the same positive carrier; neither reflection nor the
Fourier separation enlarges their frequency support. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

private theorem angular_strip_of_cycles (A B l W theta center xi eta : ℝ)
    (h : |xi/(2*Real.pi)+theta*(eta/(2*Real.pi))| ≤ A/l ∧
      |eta/(2*Real.pi)-center| ≤ B/W) :
    |xi+theta*eta| ≤ (2*Real.pi*A)/l ∧
      |eta-2*Real.pi*center| ≤ (2*Real.pi*B)/W := by
  have hp : 0 < 2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  have h₁ : xi/(2*Real.pi)+theta*(eta/(2*Real.pi)) =
      (xi+theta*eta)/(2*Real.pi) := by ring
  have h₂ : eta/(2*Real.pi)-center = (eta-2*Real.pi*center)/(2*Real.pi) := by
    field_simp [Real.pi_ne_zero]
  rw [h₁, h₂, abs_div, abs_div, abs_of_pos hp] at h
  constructor
  · exact ((div_le_iff₀ hp).mp h.1).trans_eq (by ring)
  · exact ((div_le_iff₀ hp).mp h.2).trans_eq (by ring)

theorem horizontal_scaled_angular_support (chi : SchwartzMap (ℝ×ℝ) ℂ) (A B : ℝ)
    (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (nu : SymbolSpace) (q : ℕ) (l W theta center : ℝ) (hl : 0<l) (hW : 0<W)
    (xi eta : ℝ) (h : planarAngularFourier (horizontalFrequencyKernel
      (scaledFrequencyWindow (planarInverseSchwartz chi) l W theta (2*Real.pi*center) hl.ne' hW.ne')
        nu q l theta) (xi,eta)≠0) :
    |xi+theta*eta|≤(2*Real.pi*A)/l ∧ |eta-2*Real.pi*center|≤(2*Real.pi*B)/W := by
  exact angular_strip_of_cycles A B l W theta center xi eta
    (horizontal_scaled_kernel_support chi A B hchi nu q l W theta center hl hW
      (xi/(2*Real.pi)) (eta/(2*Real.pi)) h)

theorem vertical_scaled_angular_support (chi : SchwartzMap (ℝ×ℝ) ℂ) (A B : ℝ)
    (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (nu : SymbolSpace) (q : ℕ) (l W theta center : ℝ) (hl : 0<l) (hW : 0<W)
    (xi eta : ℝ) (h : planarAngularFourier (verticalFrequencyKernel
      (scaledFrequencyWindow (planarInverseSchwartz chi) l W theta (2*Real.pi*center) hl.ne' hW.ne')
        nu q W center) (xi,eta)≠0) :
    |xi+theta*eta|≤(2*Real.pi*A)/l ∧ |eta-2*Real.pi*center|≤(2*Real.pi*B)/W := by
  exact angular_strip_of_cycles A B l W theta center xi eta
    (vertical_scaled_kernel_support chi A B hchi nu q l W theta center hl hW
      (xi/(2*Real.pi)) (eta/(2*Real.pi)) h)

theorem synthesisProfile_angular_support (chi : SchwartzMap (ℝ×ℝ) ℂ) (A B : ℝ)
    (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (nu : SymbolSpace) (q : ℕ) (l W theta center : ℝ) (hl : 0<l) (hW : 0<W)
    (z : ℝ×ℝ) (xi eta : ℝ)
    (h : planarAngularFourier (physicalPlanarPacket
      (synthesisProfile (planarInverseSchwartz chi) q nu) z.1 z.2
        l W theta (2*Real.pi*center) hl.ne' hW.ne') (xi,eta)≠0) :
    |xi+theta*eta|≤(2*Real.pi*A)/l ∧ |eta-2*Real.pi*center|≤(2*Real.pi*B)/W := by
  have heq := funext (physical_synthesisProfile (planarInverseSchwartz chi) q nu
    l W theta center hl.ne' hW.ne' z)
  rw [heq] at h
  exact synthesisWave_spectrum (S := {p | |p.1+theta*p.2|≤(2*Real.pi*A)/l ∧
      |p.2-2*Real.pi*center|≤(2*Real.pi*B)/W}) (l*W) _
    (fun p hp => horizontal_scaled_angular_support chi A B hchi nu q l W theta center
      hl hW p.1 p.2 hp) z (xi,eta) h

theorem analysisProfile_angular_support (chi : SchwartzMap (ℝ×ℝ) ℂ) (A B : ℝ)
    (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (nu : SymbolSpace) (q : ℕ) (l W theta center : ℝ) (hl : 0<l) (hW : 0<W)
    (z : ℝ×ℝ) (xi eta : ℝ)
    (h : planarAngularFourier (physicalPlanarPacket
      (analysisProfile (planarInverseSchwartz chi) q nu) z.1 z.2
        l W theta (2*Real.pi*center) hl.ne' hW.ne') (xi,eta)≠0) :
    |xi+theta*eta|≤(2*Real.pi*A)/l ∧ |eta-2*Real.pi*center|≤(2*Real.pi*B)/W := by
  have heq := funext (physical_analysisProfile (planarInverseSchwartz chi) q nu
    l W theta center hl.ne' hW.ne' z)
  rw [heq] at h
  exact analyzingWave_spectrum (S := {p | |p.1+theta*p.2|≤(2*Real.pi*A)/l ∧
      |p.2-2*Real.pi*center|≤(2*Real.pi*B)/W}) (l*W) _
    (fun p hp => vertical_scaled_angular_support chi A B hchi nu q l W theta center
      hl hW p.1 p.2 hp) z (xi,eta) h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketBinAnnulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Narrow bin support implies the common positive vertical annulus.
The loss depends on w/W, not on the number of bins. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem bin_support_annulus (w W center radius cEta CEta eta : ℝ)
    (hw : 0<w) (_hW : 0<W)
    (hlo : cEta + radius*(w/W) ≤ w*center)
    (hhi : w*center + radius*(w/W) ≤ CEta)
    (hbin : |eta-center| ≤ radius/W) :
    cEta ≤ w*eta ∧ w*eta ≤ CEta := by
  have h := abs_le.mp hbin
  have h₁ := mul_le_mul_of_nonneg_left h.1 hw.le
  have h₂ := mul_le_mul_of_nonneg_left h.2 hw.le
  have heq : w*(radius/W)=radius*(w/W) := by ring
  rw [mul_neg, heq] at h₁
  rw [heq] at h₂
  constructor <;> nlinarith only [h₁,h₂,hlo,hhi]

theorem physical_synthesis_annulus (chi : SchwartzMap (ℝ×ℝ) ℂ) (A B : ℝ)
    (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (nu : SymbolSpace) (q : ℕ) (l W theta center w cEta CEta : ℝ)
    (hl : 0<l) (hW : 0<W) (hw : 0<w)
    (hlo : cEta+(2*Real.pi*B)*(w/W) ≤ w*(2*Real.pi*center))
    (hhi : w*(2*Real.pi*center)+(2*Real.pi*B)*(w/W) ≤ CEta)
    (z : ℝ×ℝ) (xi eta : ℝ)
    (h : planarAngularFourier (physicalPlanarPacket
      (synthesisProfile (planarInverseSchwartz chi) q nu) z.1 z.2
        l W theta (2*Real.pi*center) hl.ne' hW.ne') (xi,eta)≠0) :
    |xi+theta*eta|≤(2*Real.pi*A)/l ∧ cEta≤w*eta ∧ w*eta≤CEta := by
  have hs := synthesisProfile_angular_support chi A B hchi nu q l W theta center hl hW z xi eta h
  exact ⟨hs.1,bin_support_annulus w W (2*Real.pi*center) (2*Real.pi*B)
    cEta CEta eta hw hW hlo hhi hs.2⟩

theorem physical_analysis_annulus (chi : SchwartzMap (ℝ×ℝ) ℂ) (A B : ℝ)
    (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (nu : SymbolSpace) (q : ℕ) (l W theta center w cEta CEta : ℝ)
    (hl : 0<l) (hW : 0<W) (hw : 0<w)
    (hlo : cEta+(2*Real.pi*B)*(w/W) ≤ w*(2*Real.pi*center))
    (hhi : w*(2*Real.pi*center)+(2*Real.pi*B)*(w/W) ≤ CEta)
    (z : ℝ×ℝ) (xi eta : ℝ)
    (h : planarAngularFourier (physicalPlanarPacket
      (analysisProfile (planarInverseSchwartz chi) q nu) z.1 z.2
        l W theta (2*Real.pi*center) hl.ne' hW.ne') (xi,eta)≠0) :
    |xi+theta*eta|≤(2*Real.pi*A)/l ∧ cEta≤w*eta ∧ w*eta≤CEta := by
  have hs := analysisProfile_angular_support chi A B hchi nu q l W theta center hl hW z xi eta h
  exact ⟨hs.1,bin_support_annulus w W (2*Real.pi*center) (2*Real.pi*B)
    cEta CEta eta hw hW hlo hhi hs.2⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NormalizedLatticeSpectrum
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal normalized finite lattices inherit the frequency strip,
positive annulus, and carrier bin from their fixed Fourier plateaus. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (chi : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
  (topLength width scale ratioBound C : ℝ) (order : ℕ)
  (htop : 0<topLength) (hwidth : 0<width) (hC : 0<C) (horder : 3≤order)
  (hratio : 1 ≤ ratioBound) (hscale : |scale/width| ≤ ratioBound)
  (labels : ∀ j, Finset (Label j))
  (originX originZ theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
  (site : ∀ j (l : labels j), Item j l → ℤ×ℤ)
  (hinj : ∀ j l, Function.Injective (site j l))
  (hprofile : planarProfileConstant (synthesisProfile (planarInverseSchwartz chi) q nu) (2*order) ≤ C)

local notation "P" => normalizedPacketLattice (planarInverseSchwartz chi) q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile


variable (A B : ℝ) (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
  (w cEta CEta : ℝ) (hw : 0<w)
  (hlo : ∀ k, cEta+(2*Real.pi*B)*(w/width)≤w*(2*Real.pi*center k))
  (hhi : ∀ k, w*(2*Real.pi*center k)+(2*Real.pi*B)*(w/width)≤CEta)

include hchi hw hlo hhi in
theorem normalizedPacketLattice_spectrum (j : Fin N) (l : (P).labels j)
    (a : Item j l) (k : κ) (xi eta : ℝ)
    (hs : planarAngularFourier ((P).physicalPacket 0 j l a k) (xi,eta)≠0) :
    (|xi+(P).rowSlope j l*eta|≤(2*Real.pi*A)/(P).length j ∧
      cEta≤w*eta ∧ w*eta≤CEta) ∧
    |eta-(P).frequency k|≤(2*Real.pi*B)/(P).width := by
  have hs' : planarAngularFourier (physicalPlanarPacket
      (synthesisProfile (planarInverseSchwartz chi) q nu)
      ((P).actualX j l a) ((P).actualZ j l a) ((P).length j) width (theta j l)
      (2*Real.pi*center k) ((P).length_pos j).ne' hwidth.ne') (xi,eta)≠0 := by
    change planarAngularFourier (physicalPlanarPacket
      (synthesisProfile (planarInverseSchwartz chi) q nu)
      ((P).actualX j l a) ((P).actualZ j l a+0*(P).actualX j l a)
      ((P).length j) width (0+theta j l) (2*Real.pi*center k) _ _) (xi,eta)≠0 at hs
    simpa only [zero_mul,add_zero,zero_add] using hs
  exact ⟨physical_synthesis_annulus chi A B hchi nu q ((P).length j) width
    (theta j l) (center k) w cEta CEta ((P).length_pos j) hwidth hw (hlo k) (hhi k)
    ((P).actualX j l a,(P).actualZ j l a) xi eta hs',
    (synthesisProfile_angular_support chi A B hchi nu q ((P).length j) width
      (theta j l) (center k) ((P).length_pos j) hwidth
      ((P).actualX j l a,(P).actualZ j l a) xi eta hs').2⟩

variable (chiB : SchwartzMap (ℝ×ℝ) ℂ)
  (hBprofile : planarProfileConstant (analysisProfile (planarInverseSchwartz chiB) q nu) (2*order)≤C)
local notation "alt" => normalizedAnalysisFamily (planarInverseSchwartz chi) q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile (planarInverseSchwartz chiB)
local notation "hAlt" => normalizedAnalysisFamily_bound (planarInverseSchwartz chi) q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile (planarInverseSchwartz chiB) hBprofile

include hw hlo hhi in
theorem normalizedAnalysisFamily_spectrum
    (hchiB : ∀ z, chiB z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (j : Fin N) (l : (P).labels j) (a : Item j l) (k : κ) (xi eta : ℝ)
    (hs : planarAngularFourier (((P).withProfile alt hAlt).physicalPacket 0 j l a k)
      (xi,eta)≠0) :
    (|xi+(P).rowSlope j l*eta|≤(2*Real.pi*A)/(P).length j ∧
      cEta≤w*eta ∧ w*eta≤CEta) ∧
    |eta-(P).frequency k|≤(2*Real.pi*B)/(P).width := by
  have hs' : planarAngularFourier (physicalPlanarPacket
      (analysisProfile (planarInverseSchwartz chiB) q nu)
      ((P).actualX j l a) ((P).actualZ j l a) ((P).length j) width (theta j l)
      (2*Real.pi*center k) ((P).length_pos j).ne' hwidth.ne') (xi,eta)≠0 := by
    change planarAngularFourier (physicalPlanarPacket
      (analysisProfile (planarInverseSchwartz chiB) q nu)
      ((P).actualX j l a) ((P).actualZ j l a+0*(P).actualX j l a)
      ((P).length j) width (0+theta j l) (2*Real.pi*center k) _ _) (xi,eta)≠0 at hs
    simpa only [zero_mul,add_zero,zero_add] using hs
  exact ⟨physical_analysis_annulus chiB A B hchiB nu q ((P).length j) width
    (theta j l) (center k) w cEta CEta ((P).length_pos j) hwidth hw (hlo k) (hhi k)
    ((P).actualX j l a,(P).actualZ j l a) xi eta hs',
    (analysisProfile_angular_support chiB A B hchiB nu q ((P).length j) width
      (theta j l) (center k) ((P).length_pos j) hwidth
      ((P).actualX j l a,(P).actualZ j l a) xi eta hs').2⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataModelCostPolynomial
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial dependence of the explicit model cost on the two packet
adaptation bounds. All remaining factors involve fixed geometric data. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem referenceTreeConstant_le_unit (P : PacketLatticeData N κ Label Item)
    (C : ℝ) (B K : ℕ) (Lip bound : ℝ) (hLip : 0≤Lip)
    (hprofile : P.profileBound≤bound) (habsolute : P.referenceEnvelopeConstant≤bound) :
    P.referenceTreeConstant C B K Lip≤ordinaryTreeUnitCost C B K Lip*bound := by
  have ht := transverseTailConstant_nonneg
  dsimp only [referenceTreeConstant,ordinaryTreeUnitCost]
  calc
    _ ≤ 27*288*(4*Real.pi)^2*(B:ℝ)*32*3^203*bound+
      Real.sqrt (C*(B:ℝ))*bound+
      32^106*(B:ℝ)*bound*(2+Lip)*16^53*(4*Real.pi)^2*((K+1:ℕ)+4)*
        (32*2^203)*9*transverseTailConstant := by gcongr
    _ = _ := by ring

namespace OrdinaryModelConfig
variable {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

theorem sizeAreaConstant_le_unit (d : OrdinaryModelConfig P initial) (CS bound : ℝ)
    (hCS : 0≤CS)
    (hprofile : P.profileBound≤bound) (habsolute : P.referenceEnvelopeConstant≤bound) :
    d.sizeAreaConstant CS≤d.unitSizeAreaCost CS*bound^2 := by
  have hp := P.profileBound_pos.le
  have ha := P.referenceEnvelopeConstant_pos.le
  let U := selectedFarUnitCost d.cb (Real.sqrt 2) CS d.packGap d.M d.Q
  have hU : 0≤U := by dsimp only [U,selectedFarUnitCost]; positivity
  have heFar : selectedFarConstant P d.cb (Real.sqrt 2) CS d.packGap d.M d.Q=
      U*P.profileBound^2*P.referenceEnvelopeConstant^2 := by
    dsimp only [selectedFarConstant,U,selectedFarUnitCost]
    ring
  have hFar : 2*selectedFarConstant P d.cb (Real.sqrt 2) CS d.packGap d.M d.Q≤(2*U)*(bound^2)^2 := by
    rw [heFar]
    calc
      _ ≤ 2*(U*bound^2*bound^2) := by gcongr
      _ = _ := by ring
  have hNear : selectedNearConstant P d.gap d.M d.Q ≤ selectedNearUnitCost d.gap d.M d.Q*bound^2 := by
    dsimp only [selectedNearConstant,selectedNearUnitCost]
    calc
      _ = (((2*d.gap+1:ℕ):ℝ)*(((2*d.Q+1)*d.M:ℕ):ℝ)*((4*Real.pi)^2*Real.pi^2))*P.profileBound^2 := by ring
      _ ≤ _ := by gcongr
  have hSqrt : Real.sqrt (2*selectedFarConstant P d.cb (Real.sqrt 2) CS d.packGap d.M d.Q)≤
      Real.sqrt (2*U)*bound^2 := by
    calc
      _ ≤ Real.sqrt ((2*U)*(bound^2)^2) := Real.sqrt_le_sqrt hFar
      _ = _ := by rw [Real.sqrt_mul (by positivity : 0≤2*U),Real.sqrt_sq (sq_nonneg bound)]
  calc
    _ ≤ 4*(selectedNearUnitCost d.gap d.M d.Q*bound^2+2*(Real.sqrt (2*U)*bound^2)) := by
      dsimp only [sizeAreaConstant]
      gcongr
    _ = _ := by dsimp only [unitSizeAreaCost,U]; ring

theorem modelCost_le_cubic (d : OrdinaryModelConfig P initial) (CD CS CT bound : ℝ)
    (hCS : 0≤CS) (hbound : 1≤bound)
    (hprofile : P.profileBound≤bound) (habsolute : P.referenceEnvelopeConstant≤bound) :
    d.modelCost CD CS CT≤d.unitModelCost CD CS CT*bound^3 := by
  let td := ordinaryTreeUnitCost CD ((2*d.R+1)*d.M) d.K d.Lip
  let tt := ordinaryTreeUnitCost CT ((2*d.R+1)*d.M) d.K d.Lip
  let sz := d.unitSizeAreaCost CS
  let sp := (((4*d.D0+1)^2:ℕ):ℝ)
  have ht := transverseTailConstant_nonneg
  have hLip := d.hLip
  have htd : 0≤td := by dsimp only [td,ordinaryTreeUnitCost]; positivity
  have htt : 0≤tt := by dsimp only [tt,ordinaryTreeUnitCost]; positivity
  have hsz : 0 ≤ sz := by dsimp only [sz,unitSizeAreaCost,selectedNearUnitCost]; positivity
  have hsp : 0 ≤ sp := Nat.cast_nonneg _
  have htdb := P.referenceTreeConstant_le_unit CD ((2*d.R+1)*d.M) d.K d.Lip bound d.hLip hprofile habsolute
  have httb := P.referenceTreeConstant_le_unit CT ((2*d.R+1)*d.M) d.K d.Lip bound d.hLip hprofile habsolute
  have hsizeNonneg := d.sizeAreaConstant_nonneg CS
  have hszb := d.sizeAreaConstant_le_unit CS bound hCS hprofile habsolute
  have hb3 : bound≤bound^3 := by
    have h := mul_nonneg (sub_nonneg.mpr hbound)
      (by positivity : 0≤bound^2+bound)
    nlinarith
  have hstep : d.stepConstant CD CS CT≤d.unitStepCost CD CS CT*bound^3 := by
    calc
      _ ≤ Real.sqrt 2*(2*(625*densityRadiusConstant^2*(td*bound))+
          sp*(tt*bound)*(sz*bound^2)) := by
        dsimp only [stepConstant]
        gcongr
      _ = Real.sqrt 2*((2*625*densityRadiusConstant^2*td)*bound+(sp*tt*sz)*bound^3) := by ring
      _ ≤ Real.sqrt 2*((2*625*densityRadiusConstant^2*td)*bound^3+(sp*tt*sz)*bound^3) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left hb3 (by positivity)) le_rfl) (Real.sqrt_nonneg 2)
      _ = _ := by dsimp only [unitStepCost,td,tt,sz,sp]; ring
  have hG : 0≤8*ordinaryDensityUpper/(1-ordinaryThresholdRatio) := by
    have hU : 0<ordinaryDensityUpper := zero_lt_one.trans_le (le_max_left _ _)
    have hr := sub_pos.mpr ordinaryThresholdRatio_lt_one
    positivity
  calc
    _ ≤ 1+(8*ordinaryDensityUpper/(1-ordinaryThresholdRatio))*(d.unitStepCost CD CS CT*bound^3) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hstep hG)
    _ ≤ bound^3+(8*ordinaryDensityUpper/(1-ordinaryThresholdRatio))*(d.unitStepCost CD CS CT*bound^3) :=
      add_le_add (hbound.trans hb3) le_rfl
    _ = _ := by dsimp only [unitModelCost]; ring

theorem modelCost_le_rpow (d : OrdinaryModelConfig P initial) (CD CS CT K L p : ℝ)
    (hCS : 0≤CS) (hL : 1≤L) (hKL : K≤L) (hp : 0≤p)
    (hunit : d.unitModelCost CD CS CT≤K)
    (hprofile : P.profileBound≤L^p) (habsolute : P.referenceEnvelopeConstant≤L^p) :
    d.modelCost CD CS CT≤L^(3*p+1) := by
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hpow : 1≤L^p := Real.one_le_rpow hL hp
  have hc := d.modelCost_le_cubic CD CS CT (L^p) hCS hpow hprofile habsolute
  have he : (L^p)^3=L^(3*p) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hLp.le]
    congr 1
    norm_num
    ring
  calc
    _ ≤ d.unitModelCost CD CS CT*(L^p)^3 := hc
    _ ≤ K*(L^p)^3 := mul_le_mul_of_nonneg_right hunit (by positivity)
    _ ≤ L*(L^p)^3 := mul_le_mul_of_nonneg_right hKL (by positivity)
    _ = L^(1:ℝ)*L^(3*p) := by rw [he,Real.rpow_one]
    _ = _ := by rw [←Real.rpow_add hLp]; congr 1; ring

end OrdinaryModelConfig
end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_OrdinaryModelConstructionCost
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cost of the constructed ordinary models is a fixed number.
In particular it has no dependence on the finite lattice or translation. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData

theorem OrdinaryModelConfig.unitModelCost_of_numeric_fields
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}
    (d : OrdinaryModelConfig P initial) (cStar cEta cb radius : ℝ)
    (num : OrdinaryModelNumerics cStar cEta cb radius) (M : ℕ) (CD CS CT : ℝ)
    (hcb : d.cb=cb) (hM : d.M=M) (hQ : d.Q=1) (hR : d.R=1)
    (hgap : d.gap=num.gap) (hpack : d.packGap=num.packGap)
    (hK : d.K=num.K) (hD0 : d.D0=5) (hLip : d.Lip=1) :
    d.unitModelCost CD CS CT=num.modelUnitCost M CD CS CT := by
  simp only [OrdinaryModelConfig.unitModelCost,OrdinaryModelConfig.unitStepCost,
    OrdinaryModelConfig.unitSizeAreaCost,hcb,hM,hQ,hR,hgap,hpack,hK,hD0,hLip]
  rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ScaledUnitSelector
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual selectors at angular scale `d`: measurability, unit
size, support away from the label, and the required scaled Lipschitz bound. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem scaledUnitSelector_measurable (chi : SchwartzMap ℝ ℝ) (C : ℝ)
    (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (nu : SymbolSpace) (d theta : ℝ) :
    Measurable (scaledUnitSelector chi C S q nu d theta) :=
  ((unitPacketSelector_differentiable chi C S q nu).continuous.comp (by fun_prop)).measurable

theorem scaledUnitSelector_bound (chi : SchwartzMap ℝ ℝ) (hchi : ∀ U, |chi U|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ)
    (hS : symbolCoefficientBound S q≤C) (nu : SymbolSpace) (d theta s : ℝ) :
    ‖scaledUnitSelector chi C S q nu d theta s‖≤1 :=
  unitPacketSelector_bound chi hchi C hC S q hS nu ((s-theta)/d)

theorem scaledUnitSelector_lipschitz (chi : SchwartzMap ℝ ℝ) (hchi : ∀ U, |chi U|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (hq : 1≤q)
    (hS : symbolCoefficientBound S q≤C) (nu : SymbolSpace) (d theta : ℝ) (hd : 0<d)
    (s t : ℝ) :
    ‖scaledUnitSelector chi C S q nu d theta s-scaledUnitSelector chi C S q nu d theta t‖≤
      |s-t|/d := by
  have h := (unitPacketSelector_lipschitz chi hchi C hC S q hq hS nu).dist_le_mul
    ((s-theta)/d) ((t-theta)/d)
  change ‖unitPacketSelector chi C S q nu ((s-theta)/d)-
    unitPacketSelector chi C S q nu ((t-theta)/d)‖≤_
  calc
    _ ≤ dist ((s-theta)/d) ((t-theta)/d) := by simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using h
    _ = _ := by
      rw [Real.dist_eq, show (s-theta)/d-(t-theta)/d=(s-t)/d by ring, abs_div, abs_of_pos hd]

theorem scaledUnitSelector_annular_support (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (C : ℝ) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (nu : SymbolSpace)
    (d theta s : ℝ) (hd : 0<d)
    (h : scaledUnitSelector (annularCutoff a b ha hb) C S q nu d theta s≠0) :
    (a/2)*d≤|s-theta| ∧ |s-theta|≤(2*b)*d := by
  have hl : localizedSelector (annularCutoff a b ha hb) S q nu ((s-theta)/d)≠0 := by
    intro hz
    apply h
    simp only [scaledUnitSelector, unitPacketSelector, hz, mul_zero]
  have hs := localizedSelector_support a b ha hb S q nu ((s-theta)/d) hl
  rw [abs_div, abs_of_pos hd] at hs
  exact ⟨((lt_div_iff₀ hd).mp hs.1).le, ((div_lt_iff₀ hd).mp hs.2).le⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SupportedInnerIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded tests supported on a measurable set turn local norm bounds
into literal global pairings. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem supported_inner_integral_le {X κ : Type*} [MeasurableSpace X] [Fintype κ]
    (mu : Measure X) (E : Set X) (hE : MeasurableSet E)
    (F g : X → EuclideanSpace ℂ κ) (hF : IntegrableOn F E mu)
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖≤1) (hgs : ∀ x, x∉E → g x=0) :
    Integrable (fun x => inner ℂ (F x) (g x)) mu ∧
      ‖∫ x, inner ℂ (F x) (g x) ∂mu‖≤∫ x in E, ‖F x‖ ∂mu := by
  have hp (x : X) : ‖inner ℂ (F x) (g x)‖≤‖F x‖ :=
    (norm_inner_le_norm (𝕜:=ℂ) _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (hg1 x))
  have hlocal : IntegrableOn (fun x => inner ℂ (F x) (g x)) E mu :=
    hF.norm.mono' (hF.aestronglyMeasurable.inner hg.aestronglyMeasurable)
      (Filter.Eventually.of_forall hp)
  have he (x : X) : E.indicator (fun x => inner ℂ (F x) (g x)) x=inner ℂ (F x) (g x) := by
    by_cases hx : x∈E
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx,hgs x hx,inner_zero_right]
  have hglobal := ((integrable_indicator_iff hE).2 hlocal).congr (Filter.Eventually.of_forall he)
  refine ⟨hglobal,?_⟩
  have hI : (∫ x, inner ℂ (F x) (g x) ∂mu)=∫ x in E, inner ℂ (F x) (g x) ∂mu := by
    rw [←integral_indicator hE,funext he]
  rw [hI]
  exact (norm_integral_le_integral_norm _).trans (integral_mono hlocal.norm hF.norm hp)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteSeparatedSymbolBoundL1
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer a uniform bound on the complete separated convolution sum
to the original finite symbol pairing. The two exact interchanges are
already proved, so no sum of individual row bounds is introduced. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem finite_separated_symbol_bound_l1 {ι : Type*} [Fintype ι]
    (chi : SchwartzMap ℝ ℝ) (hchi : ∀ s, |chi s|≤1) (C : ℝ) (hC : 0<C)
    (S : ι → SchwartzMap SymbolSpace ℂ) (q : ℕ) (hq : 4≤q)
    (hS : ∀ i, symbolCoefficientBound (S i) q≤C)
    (A B : ι → SchwartzMap (ℝ×ℝ) ℂ) (f : ι → ℝ×ℝ → ℂ)
    (hf : ∀ i, Integrable (f i) planeMeasure)
    (U : ι → ℝ×ℝ → ℝ) (hU : ∀ i, Measurable (U i))
    (g : ι → ℝ×ℝ → ℂ) (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, Integrable (g i) planeMeasure) (l W theta center : ι → ℝ)
    (bound : ℝ)
    (hbound : ∀ nu : SymbolSpace,
      ‖∑ i, ∫ x, unitPacketSelector chi C (S i) q nu (U i x)*
        kernelConvolution (horizontalFrequencyKernel (A i) nu q (l i) (theta i))
          (kernelConvolution (verticalFrequencyKernel (B i) nu q (W i) (center i)) (f i)) x*
          star (g i x) ∂planeMeasure‖≤bound) :
    ‖∑ i, ∫ x, (chi (U i x):ℂ)*
      (∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (S i (symbolPoint (symbolX (l i) omega.1 omega.2 (theta i))
          (symbolY (W i) omega.2 (center i)) (U i x))*
            (A i omega*B i omega*planarFourier (f i) omega)) ∂planeMeasure)*star (g i x)
      ∂planeMeasure‖ ≤ selectorNormalizer chi C*bound*(∫ nu : SymbolSpace, symbolWeight q nu) := by
  rw [finite_unit_symbol_pairing_l1 chi hchi C hC S q hq hS A B f hf U hU g hgm hg l W theta center]
  exact finite_unit_convolution_average_bound_l1 chi C hC S q hq A B f hf U hU g hgm
    l W theta center bound hbound

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAdjointPairingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert a tested ordinary forward estimate to its literal adjoint
pairing. All integrals retain their actual packet sums. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace LipschitzHilbert

theorem integrable_euclidean_inner {X κ : Type*} [MeasurableSpace X] [Fintype κ]
    (μ : Measure X) {f g : X → EuclideanSpace ℂ κ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun z => inner ℂ (f z) (g z)) μ := by
  simp only [PiLp.inner_apply,RCLike.inner_apply]
  exact integrable_finsetSum _ (fun k _ =>
    ((memLp_piLp_iff.mp hg) k).integrable_mul (((memLp_piLp_iff.mp hf) k).star))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAdjointPairingBound
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Forward-adjoint duality for the unrestricted physical packet data. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem ordinary_adjoint_pairing_bound (P : PacketLatticeData N κ Label Item)
    (S : Finset P.PacketIndex) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : MemLp f 2 (volume.prod volume)) (hg : MemLp g 2 (volume.prod volume))
    (hgm : Measurable g) (hgb : ∀ z, ‖g z‖≤1)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (hgs : ∀ z, z∉E → g z=0)
    (hint : IntegrableOn (P.ordinaryForwardSum S b u f) E (volume.prod volume)) :
    Integrable (fun z => inner ℂ (P.ordinaryAdjointSum S b u g z) (f z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (P.ordinaryAdjointSum S b u g z) (f z) ∂volume.prod volume‖≤
        ∫ z in E, ‖P.ordinaryForwardSum S b u f z‖ ∂volume.prod volume := by
  refine ⟨integrable_euclidean_inner _ (P.ordinaryAdjointSum_memLp S b u g) hf,?_⟩
  have h := P.ordinary_forward_adjoint_pairing S b hb hb1 u hu f g hf hg
  have hn := congrArg norm h
  rw [RCLike.norm_conj] at hn
  rw [←hn]
  exact (supported_inner_integral_le (volume.prod volume) E hE _ g hint hgm hgb hgs).2

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAdjointPolarization
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact polarization for masked analyzing coefficients and their
unmasked, distinct-profile adjoint synthesis. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)

theorem polarize_multiplier_coefficient (c : ℂ) (hc : ‖c‖=1)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖≤1)
    (j : Fin N) (l : P.labels j) (a : Item j l) :
    (P.polarize alt hAlt c hc).physicalMultiplierCoefficient 0 b u g j l a=
      P.physicalMultiplierCoefficient 0 b u g j l a+
        conj c • (P.withProfile alt hAlt).physicalMultiplierCoefficient 0 b u g j l a := by
  let f := fun (a : Item j l) (k : κ) (z : ℝ×ℝ) => b j l k (u z)*P.physicalPacket 0 j l a k z
  let h := fun (a : Item j l) (k : κ) (z : ℝ×ℝ) =>
    b j l k (u z)*(P.withProfile alt hAlt).physicalPacket 0 j l a k z
  have he : (fun (a : Item j l) (k : κ) (z : ℝ×ℝ) =>
      b j l k (u z)*(P.polarize alt hAlt c hc).physicalPacket 0 j l a k z)=
      fun a k z => f a k z+c*h a k z := by
    funext a k z
    rw [P.polarize_physicalPacket alt hAlt c hc]
    change b j l k (u z)*(P.physicalPacket 0 j l a k z+c*(P.withProfile alt hAlt).physicalPacket 0 j l a k z)=_
    dsimp only [f,h]
    ring
  change analyzingCoefficient (volume.prod volume) (fun _ : Item j l => P.length j*P.width)
    (fun a k z => b j l k (u z)*(P.polarize alt hAlt c hc).physicalPacket 0 j l a k z) g a=_
  rw [he]
  exact analyzingCoefficient_add_smul (volume.prod volume) (fun _ : Item j l => P.length j*P.width)
    f h g c
    (fun a k => P.physical_multiplier_analyzing_integrable 0 (fun z => b j l k (u z))
      ((hb j l k).comp hu) (fun z => hb1 j l k (u z)) g hg hg1 j l a k)
    (fun a k => (P.withProfile alt hAlt).physical_multiplier_analyzing_integrable 0 (fun z => b j l k (u z))
      ((hb j l k).comp hu) (fun z => hb1 j l k (u z)) g hg hg1 j l a k) a

theorem cross_adjoint_polarization (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖≤1)
    (z : ℝ×ℝ) :
    (4:ℂ) • (∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q)=
      (P.polarize alt hAlt 1 (by simp)).ordinaryAdjointSum S b u g z-
      (P.polarize alt hAlt (-1) (by simp)).ordinaryAdjointSum S b u g z-
      Complex.I • (P.polarize alt hAlt Complex.I (by simp)).ordinaryAdjointSum S b u g z+
      Complex.I • (P.polarize alt hAlt (-Complex.I) (by simp)).ordinaryAdjointSum S b u g z := by
  have hcross (q : P.PacketIndex) : P.crossPacketValue alt hAlt 0 b u g z q=
      WithLp.toLp 2 (fun k => P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k*
        (P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k z) := rfl
  have hterm (c : ℂ) (hc : ‖c‖=1) (q : P.PacketIndex) (k : κ) :
      (P.polarize alt hAlt c hc).packetVector
        ((P.polarize alt hAlt c hc).physicalMultiplierCoefficient 0 b u g) q z k=
      (P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k+
        conj c*(P.withProfile alt hAlt).physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k)*
      (P.physicalPacket 0 q.1 q.2.1 q.2.2 k z+c*(P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k z) := by
    change (P.polarize alt hAlt c hc).physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k*
      (P.polarize alt hAlt c hc).physicalPacket 0 q.1 q.2.1 q.2.2 k z=_
    rw [P.polarize_multiplier_coefficient alt hAlt c hc b hb hb1 u hu g hg hg1,
      P.polarize_physicalPacket alt hAlt c hc]
    simp only [PiLp.add_apply,PiLp.smul_apply,add_apply,smul_apply,smul_eq_mul]
  apply WithLp.ofLp_injective
  funext k
  simp only [hcross,ordinaryAdjointSum,WithLp.ofLp_sum,Finset.sum_apply,
    WithLp.ofLp_smul,WithLp.ofLp_add,WithLp.ofLp_sub,
    Pi.smul_apply,Pi.add_apply,Pi.sub_apply,smul_eq_mul]
  simp only [hterm]
  simp only [map_one,map_neg,Complex.conj_I,one_mul,neg_mul,neg_neg,
    Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  have h := packet_cross_polarization
    (P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k)
    ((P.withProfile alt hAlt).physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k)
    (P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
    ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k z)
  linear_combination -h

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCrossPairingBound
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four exact polarized adjoint pairings control the distinct-profile
pairing with no loss in a common bound. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem cross_pairing_bound (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (S : Finset P.PacketIndex) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (g f : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖≤1)
    (hf : MemLp f 2 (volume.prod volume)) (B : ℝ)
    (hbound : ∀ (c : ℂ) (hc : ‖c‖=1),
      ‖∫ z, inner ℂ ((P.polarize alt hAlt c hc).ordinaryAdjointSum S b u g z) (f z)
        ∂volume.prod volume‖≤B) :
    Integrable (fun z => inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q)
      (f z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q)
        (f z) ∂volume.prod volume‖≤B := by
  let A := (P.polarize alt hAlt 1 (by simp)).ordinaryAdjointSum S b u g
  let Bv := (P.polarize alt hAlt (-1) (by simp)).ordinaryAdjointSum S b u g
  let C := (P.polarize alt hAlt Complex.I (by simp)).ordinaryAdjointSum S b u g
  let D := (P.polarize alt hAlt (-Complex.I) (by simp)).ordinaryAdjointSum S b u g
  let X := fun z => ∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q
  have hA : Integrable (fun z => inner ℂ (A z) (f z)) (volume.prod volume) := integrable_euclidean_inner _
    ((P.polarize alt hAlt 1 (by simp)).ordinaryAdjointSum_memLp S b u g) hf
  have hB : Integrable (fun z => inner ℂ (Bv z) (f z)) (volume.prod volume) := integrable_euclidean_inner _
    ((P.polarize alt hAlt (-1) (by simp)).ordinaryAdjointSum_memLp S b u g) hf
  have hC : Integrable (fun z => inner ℂ (C z) (f z)) (volume.prod volume) := integrable_euclidean_inner _
    ((P.polarize alt hAlt Complex.I (by simp)).ordinaryAdjointSum_memLp S b u g) hf
  have hD : Integrable (fun z => inner ℂ (D z) (f z)) (volume.prod volume) := integrable_euclidean_inner _
    ((P.polarize alt hAlt (-Complex.I) (by simp)).ordinaryAdjointSum_memLp S b u g) hf
  refine ⟨integrable_euclidean_inner _ (P.crossSum_memLp alt hAlt 0 b u g 2 S) hf,?_⟩
  have hpoint (z : ℝ×ℝ) : (4:ℂ)*inner ℂ (X z) (f z)=
      inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
        Complex.I*inner ℂ (C z) (f z)-Complex.I*inner ℂ (D z) (f z) := by
    have h := congrArg (fun v => inner ℂ v (f z))
      (P.cross_adjoint_polarization alt hAlt S b hb hb1 u hu g hg hg1 z)
    simpa only [inner_smul_left,inner_add_left,inner_sub_left,map_ofNat,
      Complex.conj_I,neg_mul,sub_neg_eq_add,←sub_eq_add_neg] using h
  let ia := ∫ z, inner ℂ (A z) (f z) ∂volume.prod volume
  let ib := ∫ z, inner ℂ (Bv z) (f z) ∂volume.prod volume
  let ic := ∫ z, inner ℂ (C z) (f z) ∂volume.prod volume
  let idv := ∫ z, inner ℂ (D z) (f z) ∂volume.prod volume
  have hint : (4:ℂ)*(∫ z, inner ℂ (X z) (f z) ∂volume.prod volume)=
      ia-ib+Complex.I*ic-Complex.I*idv := by
    calc
      _ = ∫ z, (4:ℂ)*inner ℂ (X z) (f z) ∂volume.prod volume := (integral_const_mul _ _).symm
      _ = ∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
          Complex.I*inner ℂ (C z) (f z)-Complex.I*inner ℂ (D z) (f z)
          ∂volume.prod volume := integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = _ := by
        have hs : (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
            Complex.I*inner ℂ (C z) (f z)-Complex.I*inner ℂ (D z) (f z) ∂volume.prod volume)=
            (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
              Complex.I*inner ℂ (C z) (f z) ∂volume.prod volume)-
            (∫ z, Complex.I*inner ℂ (D z) (f z) ∂volume.prod volume) :=
          integral_sub ((hA.sub hB).add (hC.const_mul Complex.I)) (hD.const_mul Complex.I)
        have ha : (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
            Complex.I*inner ℂ (C z) (f z) ∂volume.prod volume)=
            (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z) ∂volume.prod volume)+
            (∫ z, Complex.I*inner ℂ (C z) (f z) ∂volume.prod volume) :=
          integral_add (hA.sub hB) (hC.const_mul Complex.I)
        have hb : (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z) ∂volume.prod volume)=ia-ib :=
          integral_sub hA hB
        rw [hs,ha,hb,integral_const_mul,integral_const_mul]
  have hnorm : 4*‖∫ z, inner ℂ (X z) (f z) ∂volume.prod volume‖≤
      ‖ia‖+‖ib‖+‖ic‖+‖idv‖ := by
    calc
      _ = ‖(4:ℂ)*(∫ z, inner ℂ (X z) (f z) ∂volume.prod volume)‖ := by
        rw [norm_mul]; norm_num
      _ = ‖ia-ib+Complex.I*ic-Complex.I*idv‖ := congrArg norm hint
      _ ≤ (‖ia‖+‖ib‖)+‖ic‖+‖idv‖ := by
        calc
          _ ≤ ‖ia-ib+Complex.I*ic‖+‖Complex.I*idv‖ := norm_sub_le _ _
          _ ≤ (‖ia-ib‖+‖Complex.I*ic‖)+‖Complex.I*idv‖ :=
            add_le_add (norm_add_le _ _) le_rfl
          _ ≤ ((‖ia‖+‖ib‖)+‖Complex.I*ic‖)+‖Complex.I*idv‖ := by
            gcongr; exact norm_sub_le _ _
          _ = _ := by simp only [norm_mul,Complex.norm_I,one_mul]
  have ha : ‖ia‖≤B := hbound 1 (by simp)
  have hb' : ‖ib‖≤B := hbound (-1) (by simp)
  have hc : ‖ic‖≤B := hbound Complex.I (by simp)
  have hd : ‖idv‖≤B := hbound (-Complex.I) (by simp)
  nlinarith

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundedInputEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-support bounded inputs have finite energy, bounded by support area. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert

theorem bounded_supported_input {κ : Type} [Fintype κ]
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g)
    (hbound : ∀ z, ‖g z‖≤1) (F : Set (ℝ×ℝ))
    (hF : MeasurableSet F) (hFfin : (volume.prod volume) F≠∞)
    (hsupport : ∀ z, z∉F → g z=0) :
    MemLp g 2 (volume.prod volume) ∧
      (∫ z, ‖g z‖^2 ∂volume.prod volume)≤(volume.prod volume).real F := by
  have hI : MemLp (F.indicator (fun _ => (1:ℝ))) 2 (volume.prod volume) :=
    memLp_indicator_const 2 hF 1 (Or.inr hFfin)
  have hb (z : ℝ×ℝ) : ‖g z‖≤F.indicator (fun _ => (1:ℝ)) z := by
    by_cases hz : z∈F
    · simpa only [Set.indicator_of_mem hz] using hbound z
    · simp only [Set.indicator_of_notMem hz,hsupport z hz,norm_zero,le_refl]
  have hMem : MemLp g 2 (volume.prod volume) :=
    hI.mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨hMem,?_⟩
  have hsq (z : ℝ×ℝ) : ‖g z‖^2≤F.indicator (fun _ => (1:ℝ)) z := by
    by_cases hz : z∈F
    · rw [Set.indicator_of_mem hz]
      nlinarith [hbound z,norm_nonneg (g z)]
    · simp only [Set.indicator_of_notMem hz,hsupport z hz,norm_zero,zero_pow (by decide : 2≠0),le_refl]
  have hle := integral_mono_ae (hMem.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    ((integrable_indicator_iff hF).2 (integrableOn_const (μ:=volume.prod volume) (C:=(1:ℝ)) hFfin))
    (Filter.Eventually.of_forall hsq)
  simpa only [integral_indicator_const (1:ℝ) hF,smul_eq_mul,mul_one] using hle

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataIntrinsicDensityPairing
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinct-profile bilinear density estimate, with uniform
polynomial cost and no dependence on the auxiliary jet normalization. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_intrinsic_density_pairing (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 < cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar < cEta*cb) :
    ∃ CD CS CT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound),
    ∀ (_hSpectrum : ∀ j l a k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤d.cStar/P.length j ∧ d.cEta≤d.w*et ∧ d.w*et≤d.CEta)
    (_hMargin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        Set.Icc (-xi/et-d.margin*(d.w/P.length q.1)) (-xi/et+d.margin*(d.w/P.length q.1))⊆
          scaledAngularCell (d.w/P.topLength) d.grid q.1.val (d.cell q.1 q.2.1))
    (_hBin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        |et-P.frequency k|≤d.Cv/P.width), ∀ L p : ℝ, 2≤L → 0≤p → d.unitModelCost CD CS CT≤L →
    (2^P.order*P.profileBound)*3^(2*P.order)≤L^p →
    ∀ S : Finset P.PacketIndex, S⊆initial →
    ∀ (g f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → Measurable f →
      (∀ z, ‖g z‖≤1) → (∀ z, ‖f z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F →
      (volume.prod volume) E≠∞ → (volume.prod volume) F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u → ∀ eta : ℝ, 0<eta →
      (∀ q∈S, P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤eta) →
      Integrable (fun z => inner ℂ
        (∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)
        ∂volume.prod volume‖≤L^(3*p+4)*Real.sqrt ((volume.prod volume).real F)*
          Real.sqrt ((volume.prod volume).real E)*eta^(1/4:ℝ) := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,hAll⟩ := exists_universal_ordinary_model_estimate hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,hCD,hCS,hCT,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄ heq₅ alt hAlt
    hSpectrum hMargin hBin L p hL hp hunit hprofile S hS g f hgm hfm hgb hfb
    E F hE hF hEfin hFfin hgs hfs u hu eta heta hdensity
  let Q := P.withJetControl 0 1 (by norm_num) (by simp)
  let dq := d.withJetControl 0 1 (by norm_num) (by simp)
  have hLp : 0<L := by linarith
  have hLone : 1≤L := by linarith
  have hb : P.profileBound≤(2^P.order*P.profileBound)*3^(2*P.order) := by
    have h₂ : (1:ℝ)≤2^P.order := one_le_pow₀ (by norm_num)
    have h₃ : (1:ℝ)≤3^(2*P.order) := one_le_pow₀ (by norm_num)
    calc
      _ ≤ 2^P.order*P.profileBound := le_mul_of_one_le_left P.profileBound_pos.le h₂
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg (pow_nonneg (by norm_num) _) P.profileBound_pos.le) h₃
  have hbase : Q.referenceEnvelopeConstant≤L^p := by
    simpa only [Q,referenceEnvelopeConstant,PacketLatticeData.withJetControl,one_pow,mul_one] using hprofile
  have hscale : 2*L^p≤L^(p+1) := by
    rw [Real.rpow_add hLp,Real.rpow_one]
    nlinarith [Real.rpow_nonneg hLp.le p]
  obtain ⟨hf,hfenergy⟩ := bounded_supported_input f hfm hfb F hF hFfin hfs
  have hg := (bounded_supported_input g hgm hgb E hE hEfin hgs).1
  have hFor (c : ℂ) (hc : ‖c‖=1) :
      ‖∫ z, inner ℂ ((Q.polarize alt hAlt c hc).ordinaryAdjointSum S d.selector u g z) (f z)
        ∂volume.prod volume‖≤L^(3*p+4)*Real.sqrt ((volume.prod volume).real F)*
          Real.sqrt ((volume.prod volume).real E)*eta^(1/4:ℝ) := by
    let R := Q.polarize alt hAlt c hc
    let dr := OrdinaryModelConfig.polarize (P:=Q) alt hAlt dq c hc hSpectrum hMargin hBin
    have hpr : R.profileBound≤L^(p+1) :=
      (mul_le_mul_of_nonneg_left (hb.trans hprofile) (by norm_num : (0:ℝ)≤2)).trans hscale
    have harEq : R.referenceEnvelopeConstant=2*Q.referenceEnvelopeConstant := by
      dsimp only [R,polarize,referenceEnvelopeConstant]
      ring
    have har : R.referenceEnvelopeConstant≤L^(p+1) := by
      rw [harEq]
      exact (mul_le_mul_of_nonneg_left hbase (by norm_num : (0:ℝ)≤2)).trans hscale
    have hcost := dr.modelCost_le_rpow CD CS CT L L (p+1) hCS.le hLone le_rfl
      (by linarith) hunit hpr har
    have hcost' : dr.modelCost CD CS CT≤L^(3*p+4) := by
      convert hcost using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ring
    have hm := hAll N κ Label Item R initial dr heq₁ heq₂ heq₃ heq₄ heq₅
      S hS f hf E hE hEfin u hu eta heta hdensity
    change IntegrableOn (R.ordinaryForwardSum S d.selector u f) E (volume.prod volume) ∧
      (∫ z in E, ‖R.ordinaryForwardSum S d.selector u f z‖ ∂volume.prod volume)≤
      dr.modelCost CD CS CT*Real.sqrt (∫ z, ‖f z‖^2 ∂volume.prod volume)*
        Real.sqrt ((volume.prod volume).real E)*eta^(1/4:ℝ) at hm
    have ha := R.ordinary_adjoint_pairing_bound S d.selector d.measurable d.bounded
      u hu f g hf hg hgm hgb E hE hgs hm.1
    apply ha.2.trans (hm.2.trans ?_)
    gcongr
  have h := Q.cross_pairing_bound alt hAlt S d.selector d.measurable d.bounded u hu
    g f hgm hgb hf _ hFor
  have he (z : ℝ×ℝ) (q : P.PacketIndex) :
      Q.crossPacketValue alt hAlt 0 d.selector u g z q=
        P.crossPacketValue alt hAlt 0 d.selector u g z q :=
    P.withJetControl_crossPacketValue 0 1 (by norm_num) (by simp)
      alt hAlt 0 d.selector u g z q
  have hsum (z : ℝ×ℝ) : (∑ q∈S, Q.crossPacketValue alt hAlt 0 d.selector u g z q)=
      ∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q :=
    Finset.sum_congr rfl (fun q _ => he z q)
  have hpair (z : ℝ×ℝ) :
      inner ℂ (∑ q∈S, Q.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)=
      inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z) :=
    congrArg (fun v => inner ℂ v (f z)) (hsum z)
  refine ⟨h.1.congr (Filter.Eventually.of_forall hpair),?_⟩
  have hi : (∫ z, inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)
      ∂volume.prod volume)=
      ∫ z, inner ℂ (∑ q∈S, Q.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)
        ∂volume.prod volume :=
    integral_congr_ae (Filter.Eventually.of_forall (fun z => (hpair z).symm))
  rw [hi]
  exact h.2

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataBasicPairing
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The basic finite packet bound follows from the intrinsic density
estimate and the universal density upper bound. No field regularity is needed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_intrinsic_basic_pairing (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 < cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar < cEta*cb) :
    ∃ CD CS CT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound),
    ∀ (_hSpectrum : ∀ j l a k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤d.cStar/P.length j ∧ d.cEta≤d.w*et ∧ d.w*et≤d.CEta)
    (_hMargin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        Set.Icc (-xi/et-d.margin*(d.w/P.length q.1)) (-xi/et+d.margin*(d.w/P.length q.1))⊆
          scaledAngularCell (d.w/P.topLength) d.grid q.1.val (d.cell q.1 q.2.1))
    (_hBin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        |et-P.frequency k|≤d.Cv/P.width), ∀ L p : ℝ, 2≤L → 0≤p → d.unitModelCost CD CS CT≤L →
    ordinaryDensityUpper^(1/4:ℝ)≤L →
    (2^P.order*P.profileBound)*3^(2*P.order)≤L^p →
    ∀ S : Finset P.PacketIndex, S⊆initial →
    ∀ (g f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → Measurable f →
      (∀ z, ‖g z‖≤1) → (∀ z, ‖f z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F →
      (volume.prod volume) E≠∞ → (volume.prod volume) F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      Integrable (fun z => inner ℂ
        (∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)
        ∂volume.prod volume‖≤L^(3*p+5)*Real.sqrt ((volume.prod volume).real F)*
          Real.sqrt ((volume.prod volume).real E) := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,hAll⟩ := exists_intrinsic_density_pairing hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,hCD,hCS,hCT,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄ heq₅ alt hAlt
    hSpectrum hMargin hBin L p hL hp hunit hU hprofile S hS g f hgm hfm hgb hfb
    E F hE hF hEfin hFfin hgs hfs u hu
  have hUpos : 0<ordinaryDensityUpper := zero_lt_one.trans_le (le_max_left _ _)
  have hden (q : P.PacketIndex) (_hq : q∈S) :
      P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤ordinaryDensityUpper :=
    ((P.densityTile 0 d.cell q).density_le P.topLength d.w P.width d.tau d.grid E u).trans
      (le_max_right _ _)
  have h := hAll N κ Label Item P initial d heq₁ heq₂ heq₃ heq₄ heq₅ alt hAlt
    hSpectrum hMargin hBin L p hL hp hunit hprofile S hS g f hgm hfm hgb hfb
    E F hE hF hEfin hFfin hgs hfs u hu ordinaryDensityUpper hUpos hden
  refine ⟨h.1,h.2.trans ?_⟩
  have hLp : 0<L := by linarith
  calc
    _ ≤ (L^(3*p+4)*Real.sqrt ((volume.prod volume).real F)*
        Real.sqrt ((volume.prod volume).real E))*L :=
      mul_le_mul_of_nonneg_left hU (by positivity)
    _ = _ := by
      have he : L^(3*p+5)=L^(3*p+4)*L := by
        rw [show 3*p+5=(3*p+4)+1 by ring,Real.rpow_add hLp,Real.rpow_one]
      rw [he]
      ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PacketAngularPartition
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction after the three-grid split. The selector for
each piece agrees with the original one on every retained packet. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem sum_angularPackets (P : PacketLatticeData N κ Label Item)
    (initial : Finset P.PacketIndex) (tag : ∀ j, P.labels j → DyadicLineGrid.GridChoice)
    {E : Type*} [AddCommMonoid E] (f : P.PacketIndex → E) :
    (∑ g : DyadicLineGrid.GridChoice, ∑ a∈P.angularPackets initial tag g, f a)=
      ∑ a∈initial, f a := by
  simp only [angularPackets,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

theorem crossPacketValue_congr_selector (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (t : ℝ) (b c : ∀ j, P.labels j → κ → ℝ → ℂ)
    (u : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) (a : P.PacketIndex)
    (h : ∀ k s, b a.1 a.2.1 k s=c a.1 a.2.1 k s) :
    P.crossPacketValue alt hAlt t b u g z a=P.crossPacketValue alt hAlt t c u g z a := by
  have he : b a.1 a.2.1=c a.1 a.2.1 := funext (fun k => funext (h k))
  simp only [crossPacketValue,physicalMultiplierCoefficient,he]

theorem crossPacketValue_angularSelector (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (initial : Finset P.PacketIndex) (tag : ∀ j, P.labels j → DyadicLineGrid.GridChoice)
    (grid : DyadicLineGrid.GridChoice) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (t : ℝ) (u : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (z : ℝ×ℝ) (a : P.PacketIndex) (ha : a∈P.angularPackets initial tag grid) :
    P.crossPacketValue alt hAlt t (P.angularSelector tag grid b) u g z a=
      P.crossPacketValue alt hAlt t b u g z a := by
  apply P.crossPacketValue_congr_selector alt hAlt t _ _ u g z a
  intro k s
  simp only [angularSelector,(Finset.mem_filter.mp ha).2,ite_true, if_true]

theorem sum_crossPacketValue_angularPartition (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (initial : Finset P.PacketIndex) (tag : ∀ j, P.labels j → DyadicLineGrid.GridChoice)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (t : ℝ) (u : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
    (∑ grid : DyadicLineGrid.GridChoice, ∑ a∈P.angularPackets initial tag grid,
      P.crossPacketValue alt hAlt t (P.angularSelector tag grid b) u g z a)=
      ∑ a∈initial, P.crossPacketValue alt hAlt t b u g z a := by
  calc
    _ = ∑ grid : DyadicLineGrid.GridChoice, ∑ a∈P.angularPackets initial tag grid,
        P.crossPacketValue alt hAlt t b u g z a := by
      apply Finset.sum_congr rfl
      intro grid _
      exact Finset.sum_congr rfl (fun a ha =>
        P.crossPacketValue_angularSelector alt hAlt initial tag grid b t u g z a ha)
    _ = _ := P.sum_angularPackets initial tag _

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PacketAngularBasicPairing
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The basic pairing estimate for a whole packet collection, after
constructing and recombining its three ordinary angular models. No model
configuration is assumed. All constants precede the finite packet data. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_angular_basic_pairing (hVariation : LepingleInput)
    (cStar cEta CEta cb Cv radius : ℝ) (M : ℕ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0≤CEta) (hCv : 0≤Cv)
    (hcb : 0 < cb) (hcbQuarter : cb≤1/4) (hsmall : cStar/cEta < cb/4) (hr : 0 ≤ radius)
    (hcoverSmall : 6*max radius (cStar/cEta+cb)<1)
    (num : OrdinaryModelNumerics cStar cEta cb radius) :
    ∃ CD CS CT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (S : Finset P.PacketIndex),
    ∀ w F : ℝ, 0<w → w≤P.width → 0≤F → 207≤P.order →
      (∀ k, |P.frequency k|≤F/w) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
      (∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et| ≤ cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta) →
      (∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width) →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound),
      (∀ j l a k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et| ≤ cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta) →
      (∀ j l a k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖≤1) →
      (∀ j l k s, b j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|) →
      (∀ j l k s, b j l k s≠0 → |s-P.rowSlope j l| ≤ radius*(w/P.length j)) →
      (∀ j l k s t, |s-t|≤w/P.length j → ‖b j l k s-b j l k t‖≤|s-t|/(w/P.length j)) →
    ∀ L p : ℝ, 2≤L → 0≤p → num.modelUnitCost M CD CS CT≤L →
      ordinaryDensityUpper^(1/4:ℝ)≤L → (2^P.order*P.profileBound)*3^(2*P.order)≤L^p →
    ∀ (g f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → Measurable f →
      (∀ z, ‖g z‖≤1) → (∀ z, ‖f z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → f z=0) →
    ∀ u : ℝ×ℝ → ℝ, Measurable u →
      Integrable (fun z => inner ℂ (∑ a∈S, P.crossPacketValue alt hAlt 0 b u g z a) (f z))
        (volume.prod volume) ∧
      ‖∫ z, inner ℂ (∑ a∈S, P.crossPacketValue alt hAlt 0 b u g z a) (f z)
        ∂volume.prod volume‖≤3*(L^(3*p+5)*Real.sqrt ((volume.prod volume).real Fset)*
          Real.sqrt ((volume.prod volume).real E)) := by
  have hsep : cStar < cEta*cb := by
    have h : cStar/cEta < cb := by linarith
    simpa only [mul_comm] using (div_lt_iff₀ hcEta).mp h
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,hbasic⟩ := exists_intrinsic_basic_pairing hVariation
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hsep
  refine ⟨CD,CS,CT,hCD,hCS,hCT,?_⟩
  intro N κ Label Item _ _ P S w F hw hW hF horder hfreq hlocal spectrum bin
    alt hAlt altSpectrum altBin b hb hb1 haway hradius hnear L p hL hp hcost hU hprofile
    g f hgm hfm hgb hfb E Fset hE hFset hEfin hFfin hgs hfs u hu
  classical
  obtain ⟨tag,cell,hcover⟩ := P.exists_angular_assignment w cStar cEta cb radius
    hw hcStar hcEta hcb.le hr hcoverSmall
  let d := fun gamma => angularModelConfig P S cStar cEta CEta cb Cv w F radius M
    hcStar hcEta hCEta hCv hcb hcbQuarter hsmall num hw hW hF hr horder hfreq hlocal
    tag cell hcover spectrum bin b hb hb1 haway hradius hnear gamma
  let V := fun (gamma : DyadicLineGrid.GridChoice) (z : ℝ×ℝ) =>
    ∑ a∈P.angularPackets S tag gamma,
      P.crossPacketValue alt hAlt 0 (P.angularSelector tag gamma b) u g z a
  let B := L^(3*p+5)*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E)
  have hpiece (gamma : DyadicLineGrid.GridChoice) :
      Integrable (fun z => inner ℂ (V gamma z) (f z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (V gamma z) (f z) ∂volume.prod volume‖≤B := by
    have hunit : (d gamma).unitModelCost CD CS CT≤L := by
      rw [OrdinaryModelConfig.unitModelCost_of_numeric_fields (d gamma) cStar cEta cb radius
        num M CD CS CT rfl rfl rfl rfl rfl rfl rfl rfl rfl]
      exact hcost
    apply hbasic N κ Label Item P (P.angularPackets S tag gamma) (d gamma)
      rfl rfl rfl rfl rfl alt hAlt altSpectrum _ _ L p hL hp hunit hU hprofile
      (P.angularPackets S tag gamma) (Finset.Subset.refl _) g f hgm hfm hgb hfb
      E Fset hE hFset hEfin hFfin hgs hfs u hu
    · intro a ha k xi et hs
      have heq := (Finset.mem_filter.mp ha).2
      have hspec := altSpectrum a.1 a.2.1 a.2.2 k xi et hs
      change Icc (-xi/et-cb*(w/P.length a.1)) (-xi/et+cb*(w/P.length a.1))⊆
        scaledAngularCell (w/P.topLength) gamma.val a.1.val (cell a.1 a.2.1)
      simpa only [heq] using (hcover a.1 a.2.1).2 xi et hspec.2.1 hspec.1
    · intro a _ k xi et hs
      exact altBin a.1 a.2.1 a.2.2 k xi et hs
  have hsum (z : ℝ×ℝ) : inner ℂ (∑ gamma, V gamma z) (f z)=
      inner ℂ (∑ a∈S, P.crossPacketValue alt hAlt 0 b u g z a) (f z) :=
    congrArg (fun v => inner ℂ v (f z)) (P.sum_crossPacketValue_angularPartition alt hAlt S tag b 0 u g z)
  have hsint : Integrable (fun z => ∑ gamma, inner ℂ (V gamma z) (f z)) (volume.prod volume) :=
    integrable_finsetSum _ (fun gamma _ => (hpiece gamma).1)
  have heq (z : ℝ×ℝ) : (∑ gamma, inner ℂ (V gamma z) (f z))=
      inner ℂ (∑ a∈S, P.crossPacketValue alt hAlt 0 b u g z a) (f z) := by
    rw [←sum_inner]; exact hsum z
  refine ⟨hsint.congr (Filter.Eventually.of_forall heq),?_⟩
  rw [←integral_congr_ae (Filter.Eventually.of_forall heq),
    integral_finsetSum _ (fun gamma _ => (hpiece gamma).1)]
  calc
    _ ≤ ∑ gamma : DyadicLineGrid.GridChoice,
        ‖∫ z, inner ℂ (V gamma z) (f z) ∂volume.prod volume‖ := norm_sum_le _ _
    _ ≤ ∑ _gamma : DyadicLineGrid.GridChoice, B :=
      Finset.sum_le_sum (fun gamma _ => (hpiece gamma).2)
    _ = 3*B := by simp only [Finset.sum_const,Finset.card_univ,DyadicLineGrid.gridChoice_card,nsmul_eq_mul,Nat.cast_ofNat]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedBasicConvolution
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The basic packet bound applied to the actual finite sum of separated
convolutions. The same bound holds for every translation and finite
lattice subset, so the common probability average loses no row factor. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_normalized_basic_convolution (hVariation : LepingleInput)
    (A B cEta CEta cb radius C : ℝ) (M order : ℕ)
    (hA : 0≤A) (hB : 0≤B) (hcEta : 0 < cEta) (hCEta : 0≤CEta)
    (hcb : 0 < cb) (hcbQuarter : cb≤1/4) (hr : 0 ≤ radius) (hC : 0<C)
    (horder : 207≤order) (hsmall : (2*Real.pi*A)/cEta < cb/4)
    (hcoverSmall : 6*max radius ((2*Real.pi*A)/cEta+cb)<1)
    (num : PacketLatticeData.OrdinaryModelNumerics (2*Real.pi*A) cEta cb radius) :
    ∃ K : ℝ, 0<K ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) [Fintype κ]
      (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace),
      (∀ z, chiA z≠0 → |z.1|≤A ∧ |z.2|≤B) →
      (∀ z, chiB z≠0 → |z.1|≤A ∧ |z.2|≤B) →
      (planarProfileConstant (synthesisProfile (planarInverseSchwartz chiA) q nu) (2*order)≤C) →
      (planarProfileConstant (analysisProfile (planarInverseSchwartz chiB) q nu) (2*order)≤C) →
    ∀ (topLength width scale ratioBound w F : ℝ) (htop : 0<topLength) (hwidth : 0<width),
      1 ≤ ratioBound → |scale/width| ≤ ratioBound → 0<w → w≤width → 0≤F →
    ∀ (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ),
      (∀ k, |2*Real.pi*center k|≤F/w) →
      (∀ k, cEta+(2*Real.pi*B)*(w/width)≤w*(2*Real.pi*center k)) →
      (∀ k, w*(2*Real.pi*center k)+(2*Real.pi*B)*(w/width)≤CEta) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (theta j)
        (w/(topLength/(2:ℝ)^j.val)) M) →
    ∀ (b : ∀ j, labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖≤1) →
      (∀ j l k s, b j l k s≠0 → cb*w/(topLength/(2:ℝ)^j.val)≤|theta j l-s|) →
      (∀ j l k s, b j l k s≠0 → |s-theta j l| ≤ radius*(w/(topLength/(2:ℝ)^j.val))) →
      (∀ j l k s t, |s-t|≤w/(topLength/(2:ℝ)^j.val) →
        ‖b j l k s-b j l k t‖≤|s-t|/(w/(topLength/(2:ℝ)^j.val))) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → Measurable g →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → f z=0) →
    let length := fun i : LatticeRow labels => topLength/(2:ℝ)^i.1.val
    let KA := fun (i : LatticeRow labels) (k : κ) => horizontalFrequencyKernel
      (scaledFrequencyWindow (planarInverseSchwartz chiA) (length i) width (theta i.1 i.2)
        (2*Real.pi*center k) (div_pos htop (pow_pos (by norm_num) _)).ne' hwidth.ne')
      nu q (length i) (theta i.1 i.2)
    let KB := fun (i : LatticeRow labels) (k : κ) => verticalFrequencyKernel
      (scaledFrequencyWindow (planarInverseSchwartz chiB) (length i) width (theta i.1 i.2)
        (2*Real.pi*center k) (div_pos htop (pow_pos (by norm_num) _)).ne' hwidth.ne')
      nu q width (center k)
    ‖∑ i : LatticeRow labels, ∑ k, ∫ z, b i.1 i.2 k (u z)*
      kernelConvolution (KA i k) (kernelConvolution (KB i k) (fun x => f x k)) z*
      star (g z k) ∂volume.prod volume‖≤
        K*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E) := by
  obtain ⟨CD,CS,CT,_hCD,_hCS,_hCT,hbasic⟩ := PacketLatticeData.exists_angular_basic_pairing
    hVariation (2*Real.pi*A) cEta CEta cb (2*Real.pi*B) radius M
    (by positivity) hcEta hCEta (by positivity) hcb hcbQuarter hsmall hr hcoverSmall num
  let budget : ℝ := ((2:ℝ)^order*C)*3^(2*order)
  let L : ℝ := max 2 (max (num.modelUnitCost M CD CS CT) (max (PacketLatticeData.ordinaryDensityUpper^(1/4:ℝ)) budget))
  have hL : 2≤L := le_max_left _ _
  have hLp : 0<L := by linarith
  have hcost : num.modelUnitCost M CD CS CT≤L :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hU : PacketLatticeData.ordinaryDensityUpper^(1/4:ℝ)≤L :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hbudget : budget≤L := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨3*L^8,by positivity,?_⟩
  intro N κ Label _ chiA chiB q nu hchiA hchiB hprofile hprofileB topLength width scale ratioBound
    w F htop hwidth hratio hscale hw hW hF labels theta center hfreq hlo hhi hlocal
    b hb hb1 haway hradius hnear u hu f g hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hgs hfs
    length KA KB
  have hf : MemLp f 2 (volume.prod volume) := (bounded_supported_input f hfm hfb Fset hFset hFfin hfs).1
  have hf1 (k : κ) : Integrable (fun z => f z k) (volume.prod volume) := by
    have hI : Integrable (Fset.indicator (fun _ => (1:ℝ))) (volume.prod volume) :=
      (integrable_indicator_iff hFset).2 (integrableOn_const (μ:=volume.prod volume) hFfin)
    have hfk : Measurable (fun z => f z k) :=
      (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hfm)
    apply hI.mono' hfk.aestronglyMeasurable
    filter_upwards [] with z
    by_cases hz : z∈Fset
    · simpa only [Set.indicator_of_mem hz] using (PiLp.norm_apply_le (f z) k).trans (hfb z)
    · simp only [Set.indicator_of_notMem hz,hfs z hz,WithLp.ofLp_zero,Pi.zero_apply,norm_zero,le_refl]
  apply normalized_lattice_average_bound (planarInverseSchwartz chiA) (planarInverseSchwartz chiB)
    q nu topLength width scale ratioBound C order htop hwidth hC (by omega) hratio hscale
    labels theta center hprofile hprofileB b hb hb1 u hu f g hf hf1
    (fun k => (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hgm))
    (fun k z => (PiLp.norm_apply_le (g z) k).trans (hgb z))
    (3*L^8*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E))
  intro origin S
  dsimp only
  let P := finiteNormalizedPacketLattice (planarInverseSchwartz chiA) q nu topLength width scale
    ratioBound C order htop hwidth hC (by omega) hratio hscale labels origin theta center S hprofile
  let alt := fun (j : Fin N) (l : P.labels j) (_a : finiteSiteFiber labels S j l.val) (_k : κ) =>
    analysisProfile (planarInverseSchwartz chiB) q nu
  let hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound :=
    fun _ _ _ _ => hprofileB
  have hspec := normalizedPacketLattice_spectrum (Item:=fun j l => finiteSiteFiber labels S j l) chiA q nu topLength width scale ratioBound C order
    htop hwidth hC (by omega) hratio hscale labels (fun j l => (origin j l).1)
    (fun j l => (origin j l).2) theta center (fun _ _ n => n.val)
    (fun _ _ => Subtype.val_injective) hprofile A B hchiA w cEta CEta hw hlo hhi
  have haspec := normalizedAnalysisFamily_spectrum (Item:=fun j l => finiteSiteFiber labels S j l) chiA q nu topLength width scale ratioBound C order
    htop hwidth hC (by omega) hratio hscale labels (fun j l => (origin j l).1)
    (fun j l => (origin j l).2) theta center (fun _ _ n => n.val)
    (fun _ _ => Subtype.val_injective) hprofile A B w cEta CEta hw hlo hhi chiB hprofileB hchiB
  have hbound := hbasic N κ Label (fun j l => finiteSiteFiber labels S j l) P Finset.univ w F
    hw hW hF horder hfreq hlocal
    (fun j l a k xi et hs => (hspec j l a k xi et hs).1)
    (fun j l a k xi et hs => (hspec j l a k xi et hs).2) alt hAlt
    (fun j l a k xi et hs => (haspec j l a k xi et hs).1)
    (fun j l a k xi et hs => (haspec j l a k xi et hs).2)
    b hb hb1 haway hradius hnear L 1 hL (by norm_num) hcost hU
    (by change budget≤L^(1:ℝ); simpa only [Real.rpow_one] using hbudget)
    g f hgm hfm hgb hfb E Fset hE hFset hEfin hFfin hgs hfs u hu
  have hpower : L^(3*(1:ℝ)+5)=L^(8:ℕ) := by
    rw [show 3*(1:ℝ)+5=(8:ℕ) by norm_num,Real.rpow_natCast]
  rw [hpower] at hbound
  simpa only [mul_assoc] using hbound.2

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedSymbolFormL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original finite normalized symbol form equals the common
weighted average of the actual normalized convolution forms. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]


/-- A bound for the entire normalized convolution sum passes through the
same common Fourier weight to the original finite symbol form. -/
theorem normalized_symbol_sum_bound_l1
    (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ) (chi : SchwartzMap ℝ ℝ)
    (hchi : ∀ s, |chi s|≤1) (C : ℝ) (hC : 0<C) (q : ℕ) (hq : 4≤q)
    (topLength width w : ℝ) (htop : 0<topLength) (hwidth : 0<width)
    (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (S : LatticeRow labels → κ → SchwartzMap SymbolSpace ℂ)
    (hS : ∀ i k, symbolCoefficientBound (S i k) q≤C)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (f : κ → ℝ×ℝ → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hfint : ∀ k, Integrable (f k) planeMeasure)
    (hf : ∀ z k, f k z=fData z k) (hg : Measurable g)
    (hgint : ∀ k, Integrable (fun z => g z k) planeMeasure) (bound : ℝ)
    (hbound : ∀ nu : SymbolSpace,
      ‖normalizedConvolutionSum chiA chiB q nu topLength width htop hwidth labels theta center
        (fun j l k s => scaledUnitSelector chi C (S ⟨j,l⟩ k) q nu
          (w/(topLength/(2:ℝ)^j.val)) (theta j l) s) u fData g‖≤bound) :
    ‖normalizedSymbolSumL1 chiA chiB chi topLength width w htop hwidth labels theta center S u f g‖≤
      selectorNormalizer chi C*bound*(∫ nu : SymbolSpace, symbolWeight q nu) := by
  classical
  let U := fun (i : LatticeRow labels) (z : ℝ×ℝ) =>
    symbolU (latticeLength topLength labels i) w (u z) (theta i.1 i.2)
  have hU (i : LatticeRow labels) : Measurable (U i) :=
    (hu.sub measurable_const).div_const _
  have hgm (k : κ) : Measurable (fun z => g z k) :=
    (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
  have h := finite_separated_symbol_bound_l1 (ι:=LatticeRow labels × κ) chi hchi C hC
    (fun i => S i.1 i.2) q hq (fun i => hS i.1 i.2)
    (fun i => latticeFrequencyWindow chiA topLength width htop hwidth labels theta center i.1 i.2)
    (fun i => latticeFrequencyWindow chiB topLength width htop hwidth labels theta center i.1 i.2)
    (fun i => f i.2) (fun i => hfint i.2) (fun i => U i.1) (fun i => hU i.1)
    (fun i z => g z i.2) (fun i => hgm i.2) (fun i => hgint i.2)
    (fun i => latticeLength topLength labels i.1) (fun _ => width)
    (fun i => theta i.1.1 i.1.2) (fun i => center i.2) bound (by
      intro nu
      simpa only [normalizedConvolutionSum,Fintype.sum_prod_type,U,
        scaledUnitSelector,symbolU,latticeLength,←hf] using hbound nu)
  simpa only [normalizedSymbolSumL1,Fintype.sum_prod_type,U] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedSymbolBasicL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The basic model estimate for the original finite normalized symbol
form, using the actual annular selectors and the common Fourier average. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_normalized_symbol_basic_l1_oai (hVariation : LepingleInput)
    (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (hq : 4≤q)
    (A B cEta CEta a b Cprofile Csymbol : ℝ) (M order : ℕ)
    (hA : 0≤A) (hB : 0≤B) (hcEta : 0 < cEta) (hCEta : 0≤CEta)
    (ha : 0<a) (hb : 0<b) (haQuarter : a/2≤1/4)
    (hCp : 0<Cprofile) (hCs : 0<Csymbol) (horder : 207≤order)
    (hsmall : (2*Real.pi*A)/cEta<(a/2)/4)
    (hcoverSmall : 6*max (2*b) ((2*Real.pi*A)/cEta+a/2)<1)
    (num : PacketLatticeData.OrdinaryModelNumerics (2*Real.pi*A) cEta (a/2) (2*b))
    (hchiA : ∀ z, chiA z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (hchiB : ∀ z, chiB z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (hprofiles : ∀ nu : SymbolSpace,
      planarProfileConstant (synthesisProfile (planarInverseSchwartz chiA) q nu) (2*order)≤Cprofile ∧
      planarProfileConstant (analysisProfile (planarInverseSchwartz chiB) q nu) (2*order)≤Cprofile) :
    ∃ K : ℝ, 0<K ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) [Fintype κ]
      (topLength width w F : ℝ) (htop : 0<topLength) (hwidth : 0<width),
      0<w → w≤width → 0≤F →
    ∀ (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ),
      (∀ k, |2*Real.pi*center k|≤F/w) →
      (∀ k, cEta+(2*Real.pi*B)*(w/width)≤w*(2*Real.pi*center k)) →
      (∀ k, w*(2*Real.pi*center k)+(2*Real.pi*B)*(w/width)≤CEta) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (theta j)
        (w/(topLength/(2:ℝ)^j.val)) M) →
    ∀ (S : LatticeRow labels → κ → SchwartzMap SymbolSpace ℂ),
      (∀ i k, symbolCoefficientBound (S i k) q≤Csymbol) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
    ∀ (f : κ → ℝ×ℝ → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ k, Integrable (f k) planeMeasure) →
      (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
      (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
      ‖normalizedSymbolSumL1 chiA chiB (annularCutoff a b ha hb) topLength width w htop hwidth
        labels theta center S u f g‖≤
        K*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E) := by
  obtain ⟨Kb,hKb,hbasic⟩ := exists_normalized_basic_convolution hVariation
    A B cEta CEta (a/2) (2*b) Cprofile M order hA hB hcEta hCEta
    (by positivity) haQuarter (by positivity) hCp horder hsmall hcoverSmall num
  let chi := annularCutoff a b ha hb
  have hchi : ∀ s, |chi s|≤1 := by
    intro s
    rw [abs_of_nonneg (annularCutoff_nonneg a b ha hb s)]
    exact annularCutoff_le_one a b ha hb s
  have hnormal : 0 < selectorNormalizer chi Csymbol := selectorNormalizer_pos chi Csymbol hCs
  have hI : 0≤∫ nu : SymbolSpace, symbolWeight q nu := integral_nonneg (fun nu => (symbolWeight_pos q nu).le)
  let K := selectorNormalizer chi Csymbol*Kb*((∫ nu : SymbolSpace, symbolWeight q nu)+1)
  refine ⟨K,by dsimp only [K]; positivity,?_⟩
  intro N κ Label _ topLength width w F htop hwidth hw hW hF labels theta center
    hfrequency hlo hhi hlocal S hS u hu f fData g hfint hf hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hgs hfs
  have hgint (k : κ) : Integrable (fun z => g z k) planeMeasure := by
    have hI' : Integrable (E.indicator (fun _ => (1:ℝ))) (volume.prod volume) :=
      (integrable_indicator_iff hE).2 (integrableOn_const (μ:=volume.prod volume) hEfin)
    have hmeas : Measurable (fun z => g z k) :=
      (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hgm)
    apply hI'.mono' hmeas.aestronglyMeasurable
    filter_upwards [] with z
    by_cases hz : z∈E
    · simpa only [Set.indicator_of_mem hz] using (PiLp.norm_apply_le (g z) k).trans (hgb z)
    · simp only [Set.indicator_of_notMem hz,hgs z hz,WithLp.ofLp_zero,Pi.zero_apply,norm_zero,le_refl]
  have hconv (nu : SymbolSpace) :
      ‖normalizedConvolutionSum chiA chiB q nu topLength width htop hwidth labels theta center
        (fun j l k s => scaledUnitSelector chi Csymbol (S ⟨j,l⟩ k) q nu
          (w/(topLength/(2:ℝ)^j.val)) (theta j l) s) u fData g‖≤
        Kb*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E) := by
    apply hbasic N κ Label chiA chiB q nu hchiA hchiB (hprofiles nu).1 (hprofiles nu).2
      topLength width width 1 w F htop hwidth (by norm_num)
      (by rw [div_self hwidth.ne',abs_one]) hw hW hF labels theta center hfrequency hlo hhi hlocal
      (fun j l k s => scaledUnitSelector chi Csymbol (S ⟨j,l⟩ k) q nu
        (w/(topLength/(2:ℝ)^j.val)) (theta j l) s)
    · intro j l k
      exact scaledUnitSelector_measurable chi Csymbol (S ⟨j,l⟩ k) q nu _ _
    · intro j l k s
      exact scaledUnitSelector_bound chi hchi Csymbol hCs (S ⟨j,l⟩ k) q (hS ⟨j,l⟩ k) nu _ _ s
    · intro j l k s hs
      have hh := (scaledUnitSelector_annular_support a b ha hb Csymbol (S ⟨j,l⟩ k) q nu
        (w/(topLength/(2:ℝ)^j.val)) (theta j l) s
        (div_pos hw (div_pos htop (pow_pos (by norm_num) _))) hs).1
      simpa only [mul_div_assoc,abs_sub_comm] using hh
    · intro j l k s hs
      exact (scaledUnitSelector_annular_support a b ha hb Csymbol (S ⟨j,l⟩ k) q nu
        (w/(topLength/(2:ℝ)^j.val)) (theta j l) s
        (div_pos hw (div_pos htop (pow_pos (by norm_num) _))) hs).2
    · intro j l k s t _
      exact scaledUnitSelector_lipschitz chi hchi Csymbol hCs (S ⟨j,l⟩ k) q (by omega)
        (hS ⟨j,l⟩ k) nu _ _ (div_pos hw (div_pos htop (pow_pos (by norm_num) _))) s t
    · exact hu
    · exact hfm
    · exact hgm
    · exact hfb
    · exact hgb
    · exact hE
    · exact hFset
    · exact hEfin
    · exact hFfin
    · exact hgs
    · exact hfs
  have hout := normalized_symbol_sum_bound_l1 chiA chiB chi hchi Csymbol hCs q hq
    topLength width w htop hwidth labels theta center S hS u hu f fData g hfint hf hgm hgint
    (Kb*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E)) hconv
  apply hout.trans
  have hbnd : (∫ nu : SymbolSpace, symbolWeight q nu)≤(∫ nu : SymbolSpace, symbolWeight q nu)+1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hbnd
    (show 0 ≤ selectorNormalizer chi Csymbol*Kb*Real.sqrt ((volume.prod volume).real Fset)*
      Real.sqrt ((volume.prod volume).real E) by positivity)
  dsimp only [K]
  first | (convert hmul using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hmul.trans (le_of_eq (by ring)))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PacketRepresentation.exists_normalized_symbol_basic_l1_oai := @OAI.LipschitzHilbert.PacketRepresentation.exists_normalized_symbol_basic_l1_oai
