-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_measurable_restricted_log
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:20:48.147442+00:00
-- url     : https://prove2.me/submissions/fd3a9335-3fb2-4aa3-ba59-5618ac9440b9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_actual_sharp_band_uniform_high
import Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_exists_normalized_symbol_basic_l1
import Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_scalar_band_reverse

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeDisparity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retaining logarithmically comparable amplitude masses preserves the
source model's full disparity interval. -/
noncomputable section
namespace LipschitzHilbert

theorem sqrt_mass_ratio (F E : ℝ) (hF : 0<F) (hE : 0<E) :
    0<Real.sqrt (E/F) ∧ E=(Real.sqrt (E/F))^2*F := by
  refine ⟨Real.sqrt_pos.2 (div_pos hE hF),?_⟩
  rw [Real.sq_sqrt (div_pos hE hF).le]
  field_simp

end LipschitzHilbert

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

/-- The annular multiplier and the narrow horizontal frequency support
force the normalized selector away from zero, uniformly in the scales. -/
theorem normalized_selector_lower (X V U c C : ℝ)
    (_hc : 0 < c) (hC : 0<C) (hV0 : 0≤V) (hV : V≤C)
    (hX : |X| ≤ c/4) (hAnnulus : c≤|X+V*U|) :
    3*c/(4*C)≤|U| := by
  have hm : |V*U|=V*|U| := by rw [abs_mul, abs_of_nonneg hV0]
  have htri := abs_add_le X (V*U)
  have hbound : V*|U|≤C*|U| := mul_le_mul_of_nonneg_right hV (abs_nonneg U)
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hC)).2
  nlinarith only [hX,hAnnulus,htri,hm,hbound]

/-- The positive vertical annulus also bounds the normalized selector
above; no scale or bin count enters the bound. -/
theorem normalized_selector_upper (X V U c C M : ℝ)
    (hc : 0 < c) (hV : c≤V) (hX : |X|≤C/4) (hAnnulus : |X+V*U|≤M) :
    |U|≤(M+C/4)/c := by
  have hV0 : 0≤V := hc.le.trans hV
  have hm : |V*U|=V*|U| := by rw [abs_mul, abs_of_nonneg hV0]
  have htri : |V*U|≤|X+V*U|+|X| := by
    calc
      _ = |(X+V*U)+(-X)| := by congr 1; ring
      _ ≤ |X+V*U|+|-X| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have hbound : c*|U|≤V*|U| := mul_le_mul_of_nonneg_right hV (abs_nonneg U)
  apply (le_div_iff₀ hc).2
  nlinarith only [hX,hAnnulus,htri,hm,hbound]

end LipschitzHilbert.PacketRepresentation

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

theorem weighted_symbol_identity (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (X Y U : ℝ) :
    S (symbolPoint X Y U)=∫ nu : SymbolSpace,
      (symbolWeight q nu : ℂ)*
        ((symbolWeight q nu : ℂ)*frequencyCharacter nu X Y)*
        (symbolWeight q nu : ℂ)*weightedSelector S q nu U := by
  rw [separated_symbol_fourier S X Y U]
  apply integral_congr_ae
  filter_upwards [] with nu
  have hw : (symbolWeight q nu : ℂ)≠0 := by exact_mod_cast (symbolWeight_pos q nu).ne'
  unfold weightedSelector
  field_simp

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SymbolSlice
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting one fixed Schwartz symbol to the two scale parameters.
The restriction does not enlarge any Schwartz seminorm. -/
noncomputable section
open scoped FourierTransform ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem symbolInclusion_norm : ‖symbolInclusion‖≤1 :=
  ContinuousLinearMap.norm_inl_le_one ℝ SymbolSpace (ℝ × ℝ)

theorem symbolSlice_derivative_bound (F : SchwartzMap MasterSymbolSpace ℂ)
    (p : ℝ × ℝ) (n : ℕ) (q : SymbolSpace) :
    ‖iteratedFDeriv ℝ n (symbolSlice F p) q‖≤‖iteratedFDeriv ℝ n F (q,p)‖ := by
  have hid : (symbolSlice F p : SymbolSpace → ℂ)=
      (fun z : MasterSymbolSpace => F (z+(0,p))) ∘ symbolInclusion := by
    ext x
    simp [symbolInclusion]
  have hs : ContDiff ℝ ∞ (fun z : MasterSymbolSpace => F (z+(0,p))) := by fun_prop
  have hd := symbolInclusion.iteratedFDeriv_comp_right
    (f := fun z : MasterSymbolSpace => F (z+(0,p))) hs q (i := n) (mod_cast le_top)
  rw [hid, hd]
  rw [iteratedFDeriv_comp_add_right]
  have h := (iteratedFDeriv ℝ n F (symbolInclusion q+(0,p))).norm_compContinuousLinearMap_le
    (fun _ : Fin n => symbolInclusion)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have hp : ‖symbolInclusion‖^n≤1 := pow_le_one₀ (norm_nonneg _) symbolInclusion_norm
  exact h.trans ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (by
    simp [symbolInclusion]))

theorem symbolSlice_seminorm (F : SchwartzMap MasterSymbolSpace ℂ)
    (p : ℝ × ℝ) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (symbolSlice F p)≤SchwartzMap.seminorm ℝ k n F := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (apply_nonneg _ _)
  intro q
  calc
    _ ≤ ‖q‖^k*‖iteratedFDeriv ℝ n F (q,p)‖ :=
      mul_le_mul_of_nonneg_left (symbolSlice_derivative_bound F p n q) (pow_nonneg (norm_nonneg _) _)
    _ ≤ ‖(q,p)‖^k*‖iteratedFDeriv ℝ n F (q,p)‖ := by
      gcongr
      exact le_max_left _ _
    _ ≤ _ := SchwartzMap.le_seminorm ℝ k n F (q,p)

/-- The Fourier coefficient bound is uniform over both parameters.
Only finitely many seminorms of the single master symbol enter. -/
theorem symbolSlice_coefficient_uniform (F : SchwartzMap MasterSymbolSpace ℂ) (q : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ × ℝ, symbolCoefficientBound (symbolSlice F p) q≤C := by
  let Q : Seminorm ℝ (SchwartzMap SymbolSpace ℂ) :=
    ((Finset.Iic (4*q,0)).sup (schwartzSeminormFamily ℝ SymbolSpace ℂ)).comp
      (FourierTransform.fourierCLM ℝ (SchwartzMap SymbolSpace ℂ)).toLinearMap
  have hQ : Continuous Q :=
    (Seminorm.continuous_finsetSup (fun i _ =>
      (schwartz_withSeminorms ℝ SymbolSpace ℂ).continuous_seminorm i)).comp
        (FourierTransform.fourierCLM ℝ (SchwartzMap SymbolSpace ℂ)).continuous
  obtain ⟨s,A,_hA,hbound⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ SymbolSpace ℂ) Q hQ
  let M := (s.sup (schwartzSeminormFamily ℝ MasterSymbolSpace ℂ)) F
  refine ⟨2^(4*q)*((A:ℝ)*M)+1, by dsimp [M]; positivity, ?_⟩
  intro p
  have hs : (s.sup (schwartzSeminormFamily ℝ SymbolSpace ℂ)) (symbolSlice F p)≤M := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro i hi
    exact (symbolSlice_seminorm F p i.1 i.2).trans
      (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ MasterSymbolSpace ℂ) (x := F) hi)
  have hb := (Seminorm.le_def.mp hbound) (symbolSlice F p)
  change Q (symbolSlice F p)≤(A:ℝ)*
    (s.sup (schwartzSeminormFamily ℝ SymbolSpace ℂ)) (symbolSlice F p) at hb
  have hfinal := hb.trans (mul_le_mul_of_nonneg_left hs A.coe_nonneg)
  change (Finset.Iic (4*q,0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (𝓕 (symbolSlice F p))≤(A:ℝ)*M at hfinal
  unfold symbolCoefficientBound
  exact add_le_add (mul_le_mul_of_nonneg_left hfinal (show (0:ℝ)≤2^(4*q) by positivity)) le_rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedSymbolFamily
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single compactly supported master symbol for the normalized
annular multipliers. Its slices have uniform Fourier coefficient bounds. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem masterCutoff_one (R : ℝ) (hR : 0<R) (z : MasterSymbolSpace) (hz : ‖z‖≤R) :
    masterCutoff R hR z=1 := by
  let b : ContDiffBump (0 : MasterSymbolSpace) := ⟨R,2*R,hR,by linarith⟩
  change (b z : ℂ)=1
  rw [b.one_of_mem_closedBall (by simpa using hz)]
  norm_num

theorem masterSymbol_apply (psi : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0<R)
    (z : MasterSymbolSpace) :
    masterSymbol psi R hR z=psi (masterArgument z)*masterCutoff R hR z := by
  exact SchwartzMap.smulLeftCLM_apply_apply
    (psi.hasTemperateGrowth.comp masterArgument_temperate) _ _

theorem normalizedSchwartzSymbol_apply (psi : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0<R)
    (v t X Y U : ℝ) :
    normalizedSchwartzSymbol psi R hR v t (symbolPoint X Y U)=
      psi (X+(v+t*Y)*U)*masterCutoff R hR (symbolPoint X Y U,(v,t)) := by
  rw [normalizedSchwartzSymbol, symbolSlice_apply, masterSymbol_apply]
  rfl

theorem normalizedSchwartzSymbol_one (psi : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0<R)
    (v t X Y U : ℝ) (hxyz : ‖symbolPoint X Y U‖≤R) (hp : ‖(v,t)‖≤R) :
    normalizedSchwartzSymbol psi R hR v t (symbolPoint X Y U)=psi (X+(v+t*Y)*U) := by
  have hz : ‖(symbolPoint X Y U,(v,t))‖≤R := by
    rw [Prod.norm_def]
    exact max_le hxyz hp
  rw [normalizedSchwartzSymbol_apply,
    masterCutoff_one R hR (symbolPoint X Y U,(v,t)) hz, mul_one]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedSymbolRepresentation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Fourier separation on the bounded frequency windows used for
the annular packet decomposition. Constants precede both scale parameters. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem symbolPoint_norm_le (X Y U : ℝ) :
    ‖symbolPoint X Y U‖≤|X|+|Y|+|U| := by
  have hs : ‖symbolPoint X Y U‖^2=X^2+Y^2+U^2 := by
    simp [EuclideanSpace.real_norm_sq_eq, symbolPoint, Fin.sum_univ_succ]
    ring
  nlinarith only [hs, norm_nonneg (symbolPoint X Y U), abs_nonneg X,
    abs_nonneg Y, abs_nonneg U, sq_abs X, sq_abs Y, sq_abs U,
    mul_nonneg (abs_nonneg X) (abs_nonneg Y),
    mul_nonneg (abs_nonneg X) (abs_nonneg U),
    mul_nonneg (abs_nonneg Y) (abs_nonneg U)]

/-- A cutoff which is one wherever the windowed annular symbol can be nonzero. -/
theorem normalizedSchwartzSymbol_eq (psi : SchwartzMap ℝ ℂ)
    (A B c M R : ℝ) (hR : 0<R) (hc : 0 < c)
    (hpsi : ∀ s : ℝ, M < |s| → psi s=0)
    (hsize : A+B+(M+A)/c≤R)
    (v t X Y U : ℝ) (hp : ‖(v,t)‖≤R)
    (hX : |X|≤A) (hY : |Y|≤B) (hV : c≤v+t*Y) :
    normalizedSchwartzSymbol psi R hR v t (symbolPoint X Y U)=psi (X+(v+t*Y)*U) := by
  by_cases hzero : psi (X+(v+t*Y)*U)=0
  · rw [normalizedSchwartzSymbol_apply, hzero, zero_mul]
  · have hann : |X+(v+t*Y)*U|≤M := by
      by_contra h
      exact hzero (hpsi _ (lt_of_not_ge h))
    have hU : |U|≤(M+A)/c := by
      have h := normalized_selector_upper X (v+t*Y) U c (4*A) M hc hV
        (by nlinarith only [hX]) hann
      simpa only [mul_div_cancel_left₀ A (by norm_num : (4:ℝ)≠0)] using h
    apply normalizedSchwartzSymbol_one
    · exact (symbolPoint_norm_le X Y U).trans ((add_le_add (add_le_add hX hY) hU).trans hsize)
    · exact hp

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularSelector
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

theorem annularCutoff_one (a b : ℝ) (ha : 0<a) (hb : 0<b) (U : ℝ)
    (hlo : a≤|U|) (hhi : |U|≤b) : annularCutoff a b ha hb U=1 := by
  have hi : selectorInner a ha U=0 :=
    (selectorInner a ha).zero_of_le_dist (by simpa [selectorInner, Real.dist_eq] using hlo)
  have ho : selectorOuter b hb U=1 :=
    (selectorOuter b hb).one_of_mem_closedBall (by simpa [selectorOuter, Real.dist_eq] using hhi)
  rw [annularCutoff_apply, hi, ho]
  norm_num

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FrozenSlopeMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The multiplier identity freezes the direction at the output point.
It is proved by Fubini for actual integrable time and frequency data. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem frozen_slope_multiplier (k : ℝ → ℂ) (F : ℝ×ℝ → ℂ)
    (hk : Integrable k) (hF : Integrable F planeMeasure)
    (u : ℝ×ℝ → ℝ) (x : ℝ×ℝ) :
    slopeKernelOperator k u (planarInverse F) x =
      ∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (𝓕 k (omega.1+u x*omega.2)*F omega) ∂planeMeasure := by
  let phase := fun (t : ℝ) (omega : ℝ×ℝ) =>
    (x.1-t)*omega.1+(x.2-t*u x)*omega.2
  let H := fun p : ℝ×(ℝ×ℝ) =>
    (k p.1*F p.2)*(Real.fourierChar (phase p.1 p.2):ℂ)
  have hH : Integrable H (volume.prod planeMeasure) := by
    apply (hk.mul_prod hF).mul_bdd (c := 1)
    · exact (show Continuous (fun p : ℝ×(ℝ×ℝ) =>
        (Real.fourierChar (phase p.1 p.2) : ℂ)) by dsimp [phase]; fun_prop).aestronglyMeasurable
    · filter_upwards [] with p
      exact le_of_eq (Circle.norm_coe _)
  have hleft (t : ℝ) : k t*planarInverse F (x.1-t,x.2-t*u x) =
      ∫ omega, H (t,omega) ∂planeMeasure := by
    rw [planarInverse, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with omega
    change k t*((Real.fourierChar (phase t omega):ℂ)*F omega)=_
    dsimp only [H]
    ring
  have hright (omega : ℝ×ℝ) : (∫ t, H (t,omega)) =
      Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (𝓕 k (omega.1+u x*omega.2)*F omega) := by
    rw [Real.fourier_eq]
    simp only [Real.inner_apply, Circle.smul_def, smul_eq_mul]
    rw [← integral_mul_const, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [H]
    have hp : phase t omega=(x.1*omega.1+x.2*omega.2)+(-(t*(omega.1+u x*omega.2))) := by
      dsimp [phase]
      ring
    rw [hp, Real.fourierChar.map_add_eq_mul]
    push_cast
    ring
  calc
    _ = ∫ t, ∫ omega, H (t,omega) ∂planeMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall hleft)
    _ = ∫ omega, (∫ t, H (t,omega) ∂volume) ∂planeMeasure := integral_integral_swap hH
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hright)

end LipschitzHilbert.PacketRepresentation

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

theorem schwartz_frozen_slope_multiplier (k : ℝ → ℂ) (hk : Integrable k)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (u : ℝ×ℝ → ℝ) (x : ℝ×ℝ) :
    PacketRepresentation.slopeKernelOperator k u f x =
      ∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (𝓕 k (omega.1+u x*omega.2)*planarFourier f omega) ∂volume.prod volume := by
  have h := PacketRepresentation.frozen_slope_multiplier k (planarFourier f)
    hk (planarFourier_integrable f) u x
  simpa only [funext (planarFourier_inversion f)] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LocalizedSymbolIdentity
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact separated symbol with compact annular selectors. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem localized_symbol_identity (chi : SchwartzMap ℝ ℝ) (S : SchwartzMap SymbolSpace ℂ)
    (q : ℕ) (X Y U : ℝ) :
    (chi U : ℂ)*S (symbolPoint X Y U)=∫ nu : SymbolSpace,
      (symbolWeight q nu : ℂ)*((symbolWeight q nu : ℂ)*frequencyCharacter nu X Y)*
        (symbolWeight q nu : ℂ)*localizedSelector chi S q nu U := by
  rw [weighted_symbol_identity S q X Y U, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with nu
  unfold localizedSelector
  ring

theorem localized_annular_multiplier (psi : SchwartzMap ℝ ℂ)
    (A B c C a M R : ℝ) (hR : 0<R) (hc : 0 < c) (hC : 0<C) (ha : 0<a)
    (hM : 0<M) (hA : 0≤A) (hsmall : A≤a/4)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hsize : A+B+(M+A)/c≤R)
    (v t X Y U : ℝ) (hp : ‖(v,t)‖≤R)
    (hX : |X|≤A) (hY : |Y|≤B) (hV : c≤v+t*Y) (hVC : v+t*Y≤C) (q : ℕ) :
    psi (X+(v+t*Y)*U)=∫ nu : SymbolSpace,
      (symbolWeight q nu : ℂ)*((symbolWeight q nu : ℂ)*frequencyCharacter nu X Y)*
        (symbolWeight q nu : ℂ)*localizedSelector
          (annularCutoff (3*a/(4*C)) ((M+A)/c) (by positivity) (by positivity))
          (normalizedSchwartzSymbol psi R hR v t) q nu U := by
  rw [← localized_symbol_identity]
  have htail : ∀ s : ℝ, M < |s| → psi s=0 := by
    intro s hs
    by_contra hn
    exact (not_lt_of_ge (hpsi s hn).2) hs
  rw [normalizedSchwartzSymbol_eq psi A B c M R hR hc htail hsize v t X Y U hp hX hY hV]
  by_cases hz : psi (X+(v+t*Y)*U)=0
  · rw [hz, mul_zero]
  · have hlo := normalized_selector_lower X (v+t*Y) U a C ha hC
      (hc.le.trans hV) hVC (hX.trans hsmall) (hpsi _ hz).1
    have hhi : |U|≤(M+A)/c := by
      have h := normalized_selector_upper X (v+t*Y) U c (4*A) M hc hV
        (by nlinarith only [hX]) (hpsi _ hz).2
      simpa only [mul_div_cancel_left₀ A (by norm_num : (4:ℝ)≠0)] using h
    rw [annularCutoff_one _ _ _ _ U hlo hhi, Complex.ofReal_one, one_mul]

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

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WeightedTranslatedProfiles
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed polynomial weights absorb translations of normalized packet
profiles. The estimates are uniform before all packet locations. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem translatedProfile_seminorm (F : SchwartzMap (ℝ×ℝ) ℂ)
    (a : ℝ×ℝ) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (F.compSubConstCLM ℂ a)≤
      (1+‖a‖)^k*(2^k*(Finset.Iic (k,n)).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F) := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro x
  change ‖x‖^k*‖iteratedFDeriv ℝ n (fun z => F (z-a)) x‖≤_
  rw [iteratedFDeriv_comp_sub]
  have ht : ‖x‖≤‖x-a‖+‖a‖ := by
    convert norm_add_le (x-a) a using 1 <;> first | (with_reducible_and_instances rfl) | (simp)
  have hp : ‖x‖≤(1+‖a‖)*(1+‖x-a‖) := by
    nlinarith only [ht, norm_nonneg a, norm_nonneg (x-a),
      mul_nonneg (norm_nonneg a) (norm_nonneg (x-a))]
  calc
    _ ≤ ((1+‖a‖)*(1+‖x-a‖))^k*‖iteratedFDeriv ℝ n F (x-a)‖ := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hp k) (norm_nonneg _)
    _ = (1+‖a‖)^k*((1+‖x-a‖)^k*‖iteratedFDeriv ℝ n F (x-a)‖) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k,n)) le_rfl le_rfl F (x-a))
      (by positivity)

theorem weightedTranslatedProfile_seminorm (F : SchwartzMap (ℝ×ℝ) ℂ)
    (q : ℕ) (nu : SymbolSpace) (a : ℝ×ℝ) (ha : ‖a‖≤‖nu‖)
    (k n : ℕ) (hk : k≤q) :
    SchwartzMap.seminorm ℝ k n (weightedTranslatedProfile F q nu a)≤
      2^k*(Finset.Iic (k,n)).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F := by
  have hweight : symbolWeight q nu*(1+‖a‖)^k≤1 := by
    have hpow : (1+‖a‖)^k≤(1+‖nu‖)^q :=
      (pow_le_pow_left₀ (by positivity) (by linarith only [ha]) k).trans
        (pow_le_pow_right₀ (by linarith only [norm_nonneg nu]) hk)
    unfold symbolWeight
    calc
      _ ≤ ((1+‖nu‖)^q)⁻¹*((1+‖nu‖)^q) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)
  rw [weightedTranslatedProfile, map_smul_eq_mul]
  simp only [Real.norm_eq_abs, abs_of_pos (symbolWeight_pos q nu)]
  calc
    _ ≤ symbolWeight q nu*((1+‖a‖)^k*
        (2^k*(Finset.Iic (k,n)).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F)) :=
      mul_le_mul_of_nonneg_left (translatedProfile_seminorm F a k n) (symbolWeight_pos q nu).le
    _ = (symbolWeight q nu*(1+‖a‖)^k)*
        (2^k*(Finset.Iic (k,n)).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F) := by ring
    _ ≤ 1*(2^k*(Finset.Iic (k,n)).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F) :=
      mul_le_mul_of_nonneg_right hweight (by positivity)
    _ = _ := one_mul _

/-- Any fixed continuous seminorm has a uniformly weighted translation
bound. Its finite required order determines the weight exponent. -/
theorem weightedTranslatedProfile_bounded (F : SchwartzMap (ℝ×ℝ) ℂ)
    (P : Seminorm ℝ (SchwartzMap (ℝ×ℝ) ℂ)) (hP : Continuous P) :
    ∃ q₀ : ℕ, ∃ C : ℝ, 0<C ∧ ∀ q : ℕ, q₀≤q → ∀ nu : SymbolSpace, ∀ a : ℝ×ℝ, ‖a‖≤‖nu‖ →
      P (weightedTranslatedProfile F q nu a)≤C := by
  obtain ⟨s,A,_hA,hbound⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ (ℝ×ℝ) ℂ) P hP
  let M : ℝ := ∑ i ∈ s, 2^i.1*(Finset.Iic i).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F
  have hM : 0≤M := Finset.sum_nonneg (fun i _ => by positivity)
  refine ⟨s.sup Prod.fst, (A:ℝ)*M+1, by positivity, ?_⟩
  intro q hq nu a ha
  have hs : (s.sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ))
      (weightedTranslatedProfile F q nu a)≤M := by
    apply Seminorm.finset_sup_apply_le hM
    intro i hi
    exact (weightedTranslatedProfile_seminorm F q nu a ha i.1 i.2 ((Finset.le_sup hi).trans hq)).trans
      (Finset.single_le_sum (f := fun j : ℕ×ℕ =>
        2^j.1*(Finset.Iic j).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F)
          (fun j _ => by positivity) hi)
  have hb := (Seminorm.le_def.mp hbound) (weightedTranslatedProfile F q nu a)
  change P (weightedTranslatedProfile F q nu a)≤
    (A:ℝ)*(s.sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ))
      (weightedTranslatedProfile F q nu a) at hb
  exact (hb.trans (mul_le_mul_of_nonneg_left hs A.coe_nonneg)).trans (by linarith)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_UniformTranslatedProfileBounds
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual profile constant used by the packet estimates is controlled
uniformly for the polynomially weighted translated profiles. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem profileJetCLM_apply (i : Fin 3) (F : PlanarSchwartz) :
    profileJetCLM i F=planarVerticalJet F i := by
  fin_cases i <;> rfl

theorem envelopeSeminorm_continuous (n : ℕ) : Continuous (envelopeSeminorm n) :=
  ((schwartz_withSeminorms ℝ (ℝ×ℝ) ℂ).continuous_seminorm (0,0)).comp
    ((SchwartzMap.smulLeftCLM ℂ (fun z : ℝ×ℝ => (planarPolynomialWeight n z:ℂ))).continuous)

theorem profileControlSeminorm_continuous (n : ℕ) : Continuous (profileControlSeminorm n) := by
  unfold profileControlSeminorm
  apply Seminorm.continuous_finsetSum
  intro i _
  exact (((envelopeSeminorm_continuous n).comp (profileJetCLM i).continuous).add
    ((envelopeSeminorm_continuous n).comp
      (profileHorizontalCLM.comp (profileJetCLM i)).continuous)).add
        ((envelopeSeminorm_continuous n).comp
          (profileVerticalCLM.comp (profileJetCLM i)).continuous)

theorem profileControlSeminorm_apply (n : ℕ) (F : PlanarSchwartz) :
    planarProfileConstant F n=profileControlSeminorm n F+9 := by
  have hpoint (i : Fin 3) :
      planarEnvelopeConstant (planarVerticalJet F i) n+
        planarEnvelopeConstant (planarHorizontalDerivative (planarVerticalJet F i)) n+
        planarEnvelopeConstant (planarVerticalDerivative (planarVerticalJet F i)) n=
      (envelopeSeminorm n (profileJetCLM i F)+
        envelopeSeminorm n (profileHorizontalCLM (profileJetCLM i F))+
        envelopeSeminorm n (profileVerticalCLM (profileJetCLM i F)))+3 := by
    simp only [profileJetCLM_apply]
    change (envelopeSeminorm n (planarVerticalJet F i)+1)+
      (envelopeSeminorm n (planarHorizontalDerivative (planarVerticalJet F i))+1)+
      (envelopeSeminorm n (planarVerticalDerivative (planarVerticalJet F i))+1)=_
    change (envelopeSeminorm n (planarVerticalJet F i)+1)+
      (envelopeSeminorm n (planarHorizontalDerivative (planarVerticalJet F i))+1)+
      (envelopeSeminorm n (planarVerticalDerivative (planarVerticalJet F i))+1)=
        (envelopeSeminorm n (planarVerticalJet F i)+
          envelopeSeminorm n (planarHorizontalDerivative (planarVerticalJet F i))+
          envelopeSeminorm n (planarVerticalDerivative (planarVerticalJet F i)))+3
    ring
  unfold planarProfileConstant
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
  simp [profileControlSeminorm]

theorem uniform_translated_profile_bound (F : PlanarSchwartz) (n : ℕ) :
    ∃ q₀ : ℕ, ∃ C : ℝ, 0<C ∧ ∀ q : ℕ, q₀≤q → ∀ nu : SymbolSpace, ∀ a : ℝ×ℝ, ‖a‖≤‖nu‖ →
      planarProfileConstant (weightedTranslatedProfile F q nu a) n≤C := by
  obtain ⟨q₀,C,hC,hbound⟩ := weightedTranslatedProfile_bounded F
    (profileControlSeminorm n) (profileControlSeminorm_continuous n)
  refine ⟨q₀,C+9,by linarith only [hC],?_⟩
  intro q hq nu a ha
  rw [profileControlSeminorm_apply]
  exact add_le_add (hbound q hq nu a ha) le_rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_NormalizedPacketProfiles
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single Fourier parameter determines both normalized wave profiles.
Their common bound is chosen before all spatial scales and frequency bins. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem uniform_normalized_profile_pair (F G : SchwartzMap (ℝ×ℝ) ℂ) (n : ℕ) :
    ∃ q₀ : ℕ, ∃ C : ℝ, 0<C ∧ ∀ q : ℕ, q₀≤q → ∀ nu : SymbolSpace,
      planarProfileConstant (synthesisProfile F q nu) n ≤ C ∧
        planarProfileConstant (analysisProfile G q nu) n ≤ C := by
  obtain ⟨qF,CF,hCF,hF⟩ := uniform_translated_profile_bound F n
  obtain ⟨qG,CG,hCG,hG⟩ := uniform_translated_profile_bound (reflectedConjugateProfile G) n
  refine ⟨max qF qG,max CF CG,lt_max_of_lt_left hCF,?_⟩
  intro q hq nu
  constructor
  · apply (hF q ((le_max_left _ _).trans hq) nu (-nu 0,0) ?_).trans (le_max_left _ _)
    simpa only [Prod.norm_def, norm_neg, norm_zero, max_eq_left (norm_nonneg _)] using
      PiLp.norm_apply_le nu 0
  · apply (hG q ((le_max_right _ _).trans hq) nu (0,nu 1) ?_).trans (le_max_right _ _)
    simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using
      PiLp.norm_apply_le nu 1

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlopeLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The slope-label multiplicity assumption in §2 of the manuscript
gives a uniform number of labels active at a fixed source direction.
This includes vector-valued selectors: taking the union over all bin
components does not increase the count.  The last lemmas split the
active labels at every scale into a fixed finite set of lattice slots. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.SourceSlopeLabels

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

theorem window_card_le (labels : Finset ι) (slope : ι → ℝ)
    {t d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : LocalMultiplicity labels slope d M) (hK : radius ≤ K) :
    (window labels slope t d radius).card ≤ (2 * K + 1) * M := by
  classical
  let active := window labels slope t d radius
  let bin : ι → ℤ := fun i => ⌊(slope i - t) / d⌋
  let bins : Finset ℤ := Finset.Icc (-(K : ℤ)) K
  have hmaps : (active : Set ι).MapsTo bin bins := by
    intro i hi
    have hwin : |slope i - t| ≤ radius * d := (Finset.mem_filter.mp hi).2
    have habs : |slope i - t| ≤ (K : ℝ) * d :=
      hwin.trans (mul_le_mul_of_nonneg_right hK hd.le)
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    have hlow : -(K : ℝ) ≤ (slope i - t) / d := by
      apply (le_div_iff₀ hd).mpr
      linarith
    have hupp : (slope i - t) / d < (K : ℝ) + 1 := by
      apply (div_lt_iff₀ hd).mpr
      nlinarith
    exact Finset.mem_Icc.mpr ⟨Int.le_floor.mpr (by simpa using hlow),
      Int.floor_le_iff.mpr (by simpa using hupp)⟩
  have hfiber (b : ℤ) : (active.filter (fun i => bin i = b)).card ≤ M := by
    apply (Finset.card_le_card (show active.filter (fun i => bin i = b) ⊆
      labels.filter (fun i => t + (b : ℝ) * d ≤ slope i ∧
        slope i < (t + (b : ℝ) * d) + d) from ?_)).trans
      (hlocal (t + (b : ℝ) * d))
    intro i hi
    obtain ⟨hia, hib⟩ := Finset.mem_filter.mp hi
    have hil : i ∈ labels := (Finset.mem_filter.mp hia).1
    have h0 := Int.floor_le ((slope i - t) / d)
    have h1 := Int.lt_floor_add_one ((slope i - t) / d)
    change ⌊(slope i - t) / d⌋ = b at hib
    rw [hib] at h0 h1
    have h0' := (le_div_iff₀ hd).mp h0
    have h1' := (div_lt_iff₀ hd).mp h1
    exact Finset.mem_filter.mpr ⟨hil, by constructor <;> nlinarith⟩
  have hcount : bins.card = 2 * K + 1 := by
    have hcount' : (bins.card : ℤ) = 2 * (K : ℤ) + 1 := by
      dsimp [bins]
      rw [Int.card_Icc_of_le (a := -(K : ℤ)) (b := (K : ℤ)) (by omega)]
      omega
    exact_mod_cast hcount'
  calc
    active.card = ∑ b ∈ bins, (active.filter (fun i => bin i = b)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _b ∈ bins, M := Finset.sum_le_sum fun b _ => hfiber b
    _ = (2 * K + 1) * M := by simp [hcount]

end LipschitzHilbert.SourceSlopeLabels

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceL2Gram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact L2 Gram identities for the finite physical packet sums. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem memLp_inner_integral (mu : Measure X) (f g : X → E)
    (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    inner ℂ (hf.toLp f) (hg.toLp g)=∫ x, inner ℂ (f x) (g x) ∂mu := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hfx hgx
  rw [hfx,hgx]

theorem memLp_toL2_norm_sq (mu : Measure X) (f : X → E) (hf : MemLp f 2 mu) :
    ‖hf.toLp f‖^2=∫ x, ‖f x‖^2 ∂mu := by
  have h := memLp_inner_integral mu f f hf hf
  simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow] at h
  change ((‖hf.toLp f‖^2 : ℝ) : ℂ)=(∫ x, ((‖f x‖^2 : ℝ) : ℂ) ∂mu) at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BoundedSupportedCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate integrability follows from the vector indicator bound,
without a factor depending on the number of coordinates. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem bounded_supported_coordinate_integrable {κ : Type} [Fintype κ]
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hbound : ∀ z, ‖g z‖≤1)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (hEfin : planeMeasure E≠∞)
    (hsupport : ∀ z, z∉E → g z=0) (k : κ) : Integrable (fun z => g z k) planeMeasure := by
  have hI : Integrable (E.indicator (fun _ => (1:ℝ))) planeMeasure :=
    (integrable_indicator_iff hE).2 (integrableOn_const (μ:=planeMeasure) hEfin)
  have hm : Measurable (fun z => g z k) :=
    (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
  apply hI.mono' hm.aestronglyMeasurable
  filter_upwards [] with z
  by_cases hz : z∈E
  · simpa only [Set.indicator_of_mem hz] using (PiLp.norm_apply_le (g z) k).trans (hbound z)
  · simp only [Set.indicator_of_notMem hz,hsupport z hz,WithLp.ofLp_zero,Pi.zero_apply,norm_zero,le_refl]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SmoothSlopeSymbol
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth extension of the slope denominator gives the full normalized
symbol, including its slope partition and vertical frequency window. -/
noncomputable section
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem positiveDenominator_eq (c : ℝ) (hc : 0 < c) (s : ℝ) (hs : c ≤ s) :
    positiveDenominator c s=s := by
  unfold positiveDenominator
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by positivity : (0:ℝ) < c/2)).2
    (by linarith only [hs])), one_mul]
  ring

theorem partitionedMasterSymbol_apply (psi rho beta : SchwartzMap ℝ ℂ)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0<R) (z : MasterSymbolSpace) :
    partitionedMasterSymbol psi rho beta c hc R hR z=
      masterCutoff R hR z*(psi (masterArgument z)*rho (masterSlopeArgument c z)*beta (z.1 1)) := rfl

theorem partitionedSymbol_uniform (psi rho beta : SchwartzMap ℝ ℂ)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0<R) (q : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ v t : ℝ,
      symbolCoefficientBound (partitionedSymbol psi rho beta c hc R hR v t) q≤C := by
  obtain ⟨C,hC,h⟩ := symbolSlice_coefficient_uniform (partitionedMasterSymbol psi rho beta c hc R hR) q
  exact ⟨C,hC,fun v t => h (v,t)⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PartitionedSymbolIdentity
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact separation of the full symbol, including the frequency-slope
partition and the vertical bin window, with annular selector support. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem partitionedSymbol_factor (psi rho beta : SchwartzMap ℝ ℂ)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0<R) (v t X Y U : ℝ) :
    partitionedSymbol psi rho beta c hc R hR v t (symbolPoint X Y U)=
      normalizedSchwartzSymbol psi R hR v t (symbolPoint X Y U)*
        rho (-X/positiveDenominator c (v+t*Y))*beta Y := by
  rw [partitionedSymbol, symbolSlice_apply, partitionedMasterSymbol_apply,
    normalizedSchwartzSymbol_apply]
  change masterCutoff R hR (symbolPoint X Y U,(v,t))*
      (psi (X+(v+t*Y)*U)*rho (-X/positiveDenominator c (v+t*Y))*beta Y)=
    psi (X+(v+t*Y)*U)*masterCutoff R hR (symbolPoint X Y U,(v,t))*
      rho (-X/positiveDenominator c (v+t*Y))*beta Y
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_RescaledAnnularSymbol
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed angular enlargement is an exact change of normalized
coordinates. The annular cutoff and the compact master symbol are still
one on every contributing frequency. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem rescaled_symbol_coordinates (H l w W theta center u xi eta : ℝ)
    (hH : H≠0) (hl : l≠0) (hw : w≠0) (hW : W≠0) :
    symbolX l xi eta theta+
      (H*w*center+(H*w/W)*symbolY W eta center)*symbolU l (H*w) u theta=
      l*(xi+u*eta) := by
  unfold symbolX symbolY symbolU
  field_simp
  ring

theorem rescaled_localized_symbol_eq (psi : SchwartzMap ℝ ℂ)
    (A B c C a M R H : ℝ) (hR : 0<R) (hH : 0<H)
    (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hA : 0≤A) (hsmall : A≤a/4)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hsize : A+B+(M+A)/(H*c)≤R)
    (l w W theta center u xi eta : ℝ) (hl : 0<l) (hw : 0<w) (hW : 0<W)
    (hparam : ‖(H*w*center,H*w/W)‖≤R)
    (hX : |symbolX l xi eta theta|≤A) (hY : |symbolY W eta center|≤B)
    (hlo : c≤w*eta) (hhi : w*eta≤C) :
    (annularCutoff (3*a/(4*(H*C))) ((M+A)/(H*c)) (by positivity) (by positivity)
      (symbolU l (H*w) u theta):ℂ)*
      normalizedSchwartzSymbol psi R hR (H*w*center) (H*w/W)
        (symbolPoint (symbolX l xi eta theta) (symbolY W eta center) (symbolU l (H*w) u theta))=
      psi (l*(xi+u*eta)) := by
  have hvertical : H*w*center+(H*w/W)*symbolY W eta center=H*(w*eta) := by
    unfold symbolY
    field_simp
    ring
  have hVlo : H*c≤H*w*center+(H*w/W)*symbolY W eta center := by
    rw [hvertical]
    exact mul_le_mul_of_nonneg_left hlo hH.le
  have hVhi : H*w*center+(H*w/W)*symbolY W eta center≤H*C := by
    rw [hvertical]
    exact mul_le_mul_of_nonneg_left hhi hH.le
  have heq := localized_annular_multiplier psi A B (H*c) (H*C) a M R hR
    (mul_pos hH hc) (mul_pos hH hC) ha hM hA hsmall hpsi hsize
    (H*w*center) (H*w/W) (symbolX l xi eta theta) (symbolY W eta center)
    (symbolU l (H*w) u theta) hparam hX hY hVlo hVhi 0
  rw [←localized_symbol_identity] at heq
  rw [rescaled_symbol_coordinates H l w W theta center u xi eta hH.ne' hl.ne' hw.ne' hW.ne'] at heq
  exact heq.symm


/-- A vertical frequency window inherits the original annulus from its
center and width, with the exact endpoint allowance. -/
theorem vertical_annulus_from_window (w W center eta B c C : ℝ)
    (hw : 0<w) (hW : 0<W)
    (hlo : c+B*(w/W)≤w*center) (hhi : w*center+B*(w/W)≤C)
    (hY : |symbolY W eta center|≤B) : c≤w*eta ∧ w*eta≤C := by
  have hy := abs_le.mp hY
  have hp : 0≤w/W := (div_pos hw hW).le
  have hcancel : (w/W)*symbolY W eta center=w*(eta-center) := by
    unfold symbolY
    field_simp
  have hleft := mul_le_mul_of_nonneg_left hy.1 hp
  have hright := mul_le_mul_of_nonneg_left hy.2 hp
  rw [hcancel] at hleft hright
  constructor <;> nlinarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_RescaledPartitionedSymbol
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The slope partition is rescaled together with the angular variable,
so its argument remains the original frequency slope divided by w/l. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem rescaled_partitioned_symbol_eq (psi rho beta : SchwartzMap ℝ ℂ)
    (A B c C a M R H : ℝ) (hR : 0<R) (hH : 0<H)
    (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hA : 0≤A) (hsmall : A≤a/4)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hsize : A+B+(M+A)/(H*c)≤R)
    (l w W theta center u xi eta : ℝ) (hl : 0<l) (hw : 0<w) (hW : 0<W)
    (hparam : ‖(H*w*center,H*w/W)‖≤R)
    (hX : |symbolX l xi eta theta|≤A) (hY : |symbolY W eta center|≤B)
    (hlo : c≤w*eta) (hhi : w*eta≤C) :
    (annularCutoff (3*a/(4*(H*C))) ((M+A)/(H*c)) (by positivity) (by positivity)
      (symbolU l (H*w) u theta):ℂ)*
      partitionedSymbol psi (dilatedSlopeWindow rho H hH.ne') beta (H*c) (mul_pos hH hc) R hR
        (H*w*center) (H*w/W)
        (symbolPoint (symbolX l xi eta theta) (symbolY W eta center) (symbolU l (H*w) u theta))=
      psi (l*(xi+u*eta))*rho (-symbolX l xi eta theta/(w*eta))*beta (symbolY W eta center) := by
  have hvertical : H*w*center+(H*w/W)*symbolY W eta center=H*(w*eta) := by
    unfold symbolY
    field_simp
    ring
  have hVlo : H*c≤H*w*center+(H*w/W)*symbolY W eta center := by
    rw [hvertical]
    exact mul_le_mul_of_nonneg_left hlo hH.le
  have hwe : 0<w*eta := hc.trans_le hlo
  rw [partitionedSymbol_factor,positiveDenominator_eq (H*c) (mul_pos hH hc) _ hVlo,
    dilatedSlopeWindow_apply,hvertical]
  have hrho : H*(-symbolX l xi eta theta/(H*(w*eta)))=
      -symbolX l xi eta theta/(w*eta) := by field_simp
  rw [hrho]
  rw [←mul_assoc,←mul_assoc,
    rescaled_localized_symbol_eq psi A B c C a M R H hR hH hc hC ha hM hA hsmall
      hpsi hsize l w W theta center u xi eta hl hw hW hparam hX hY hlo hhi]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlopePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete compact smooth partition on an arithmetic slope lattice.
The finite sum is exactly one on its prescribed interval. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem slopePartition_apply (x : ℝ) : slopePartition x=(slopePartitionReal x : ℂ) := rfl

theorem slopePartition_support (x : ℝ) (hx : slopePartition x≠0) : |x|≤1 := by
  by_contra h
  have habs : 1 < |x| := lt_of_not_ge h
  have hxx : x≤-1 ∨ 1≤x := by
    rcases lt_or_ge x 0 with hn | hp
    · rw [abs_of_neg hn] at habs
      exact Or.inl (by linarith)
    · rw [abs_of_nonneg hp] at habs
      exact Or.inr habs.le
  have heq := slopePartitionReal_eq_zero x hxx
  exact hx (by rw [slopePartition_apply,heq,Complex.ofReal_zero])

theorem slopePartitionReal_sum (x : ℝ) (N : ℕ) :
    ∑ n∈Finset.range N, slopePartitionReal (x-(n:ℝ))=
      Real.smoothTransition (x+1)-Real.smoothTransition (x+1-N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,slopePartitionReal]
    push_cast
    rw [show x+1-((N:ℝ)+1)=x-N by ring,show x-N+1=x+1-N by ring]
    ring

theorem slopePartition_sum_one (K : ℕ) (x : ℝ) (hx : |x|≤K) :
    ∑ n∈Finset.range (2*K+1), slopePartition (x+K-(n:ℝ))=1 := by
  simp only [slopePartition_apply,←Complex.ofReal_sum]
  rw [slopePartitionReal_sum]
  have hbounds := abs_le.mp hx
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by push_cast; linarith)]
  norm_num

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact modulated convolution kernels for the fixed vertical bin
profiles, with a uniform L1 norm at every width and carrier. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem modulatedTimeKernel_fourier (K : ℝ → ℂ) (W center eta : ℝ) (hW : 0<W) :
    𝓕 (modulatedTimeKernel K W center) eta=𝓕 K (W*(eta-center)) := by
  rw [←scaledTimeKernel_fourier K W hW (eta-center)]
  rw [Real.fourier_eq,Real.fourier_eq]
  simp only [Real.inner_apply,modulatedTimeKernel]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [←mul_smul,←Real.fourierChar.map_add_eq_mul]
  congr 2
  ring

theorem modulatedTimeKernel_norm (K : ℝ → ℂ) (W center t : ℝ) (hW : 0<W) :
    ‖modulatedTimeKernel K W center t‖=W⁻¹*‖K (t/W)‖ := by
  rw [modulatedTimeKernel,Circle.norm_smul,scaledTimeKernel,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg hW.le]

theorem modulatedTimeKernel_l1 (K : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W) :
    (∫ t, ‖modulatedTimeKernel K W center t‖)=∫ t, ‖K t‖ := by
  simp_rw [modulatedTimeKernel_norm K W center _ hW]
  rw [integral_const_mul,Measure.integral_comp_div (fun t => ‖K t‖) W,
    abs_of_pos hW,smul_eq_mul]
  rw [←mul_assoc,inv_mul_cancel₀ hW.ne',one_mul]

theorem verticalProfileKernel_fourier (q : SchwartzMap ℝ ℂ) (W center eta : ℝ) (hW : 0<W) :
    𝓕 (verticalProfileKernel q W center) eta=q (W*(eta-center)) := by
  rw [verticalProfileKernel,modulatedTimeKernel_fourier _ W center eta hW]
  have h : (𝓕 (𝓕⁻ q : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ)=q := fourier_fourierInv_eq q
  exact congrArg (fun f : SchwartzMap ℝ ℂ => f (W*(eta-center))) h

theorem verticalConvolution_uniform_bound (K : ℝ → ℂ) (hK : Integrable K)
    (f : ℝ×ℝ → ℂ) (C : ℝ) (hf : ∀ z, ‖f z‖≤C) (z : ℝ×ℝ) :
    ‖verticalConvolution K f z‖≤C*∫ t, ‖K t‖ := by
  have h := norm_integral_le_of_norm_le (hK.norm.const_mul C)
    (Filter.Eventually.of_forall (fun t => show ‖K t*f (z.1,z.2-t)‖≤C*‖K t‖ from by
      rw [norm_mul,mul_comm C]
      exact mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)))
  simpa only [verticalConvolution,integral_const_mul] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteTimeKernelMoment
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first absolute moment of the retained time kernel is bounded
by twice the largest scale, independently of the number of scales. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem finiteTimeKernel_measurable (k : SchwartzMap ℝ ℂ) (N : ℕ) (topLength : ℝ) :
    Measurable (finiteTimeKernel k N topLength) := by
  unfold finiteTimeKernel scaledTimeKernel
  fun_prop

theorem finiteTimeKernel_integrable (k : SchwartzMap ℝ ℂ) (N : ℕ) (topLength : ℝ)
    (htop : 0<topLength) : Integrable (finiteTimeKernel k N topLength) := by
  exact integrable_finsetSum _ (fun j _ => scaledTimeKernel_integrable k k.integrable _
    (ne_of_gt (div_pos htop (pow_pos (by norm_num) j.val))))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalConvolutionL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical convolution acts on actual measurable planar functions.
Its L1 and uniform bounds are independent of bin width and carrier. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalConvolution_joint_integrable (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (hf : Integrable f planeMeasure) :
    Integrable (fun p : ℝ×(ℝ×ℝ) => K p.1*f (p.2.1,p.2.2-p.1))
      (volume.prod planeMeasure) := by
  have hm : Measurable (fun p : ℝ×(ℝ×ℝ) => K p.1*f (p.2.1,p.2.2-p.1)) := by
    exact (hKm.comp measurable_fst).mul (hfm.comp (by fun_prop))
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun t =>
      ((verticalTranslation_measurePreserving t).integrable_comp_of_integrable hf).const_mul (K t)
  · have heq (t : ℝ) : (∫ z, ‖K t*f (z.1,z.2-t)‖ ∂planeMeasure)=
        ‖K t‖*(∫ z, ‖f z‖ ∂planeMeasure) := by
      simp_rw [norm_mul]
      rw [integral_const_mul,integral_verticalTranslation t (fun z => ‖f z‖)]
    simp_rw [heq]
    exact hK.norm.mul_const _

theorem verticalConvolution_integrable (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (hf : Integrable f planeMeasure) :
    Integrable (verticalConvolution K f) planeMeasure :=
  (verticalConvolution_joint_integrable K hK hKm f hfm hf).integral_prod_right

theorem verticalConvolution_l1_bound (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (hf : Integrable f planeMeasure) :
    (∫ z, ‖verticalConvolution K f z‖ ∂planeMeasure)≤
      (∫ t, ‖K t‖)*(∫ z, ‖f z‖ ∂planeMeasure) := by
  have hi := verticalConvolution_joint_integrable K hK hKm f hfm hf
  calc
    _ ≤ ∫ z, ∫ t, ‖K t*f (z.1,z.2-t)‖ ∂volume ∂planeMeasure := by
      apply integral_mono (verticalConvolution_integrable K hK hKm f hfm hf).norm
        hi.norm.integral_prod_right
      exact fun z => norm_integral_le_integral_norm _
    _ = ∫ t, ∫ z, ‖K t*f (z.1,z.2-t)‖ ∂planeMeasure ∂volume :=
      integral_integral_swap hi.norm.swap
    _ = _ := by
      simp_rw [norm_mul,integral_const_mul,integral_verticalTranslation _ (fun z => ‖f z‖)]
      rw [integral_mul_const]

theorem verticalConvolution_horizontal_support (K : ℝ → ℂ) (f : ℝ×ℝ → ℂ)
    (S : Set ℝ) (hf : ∀ z, z.1∉S → f z=0) :
    ∀ z, z.1∉S → verticalConvolution K f z=0 := by
  intro z hz
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun t => by
    change K t*f (z.1,z.2-t)=0
    rw [hf (z.1,z.2-t) hz,mul_zero]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalInverseMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact inverse-frequency representation of vertical convolution. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem vertical_inverse_multiplier (k : ℝ → ℂ) (F : ℝ×ℝ → ℂ)
    (hk : Integrable k) (hF : Integrable F planeMeasure)
    (x : ℝ×ℝ) :
    verticalConvolution k (planarInverse F) x =
      ∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (𝓕 k (omega.2)*F omega) ∂planeMeasure := by
  let phase := fun (t : ℝ) (omega : ℝ×ℝ) =>
    x.1*omega.1+(x.2-t)*omega.2
  let H := fun p : ℝ×(ℝ×ℝ) =>
    (k p.1*F p.2)*(Real.fourierChar (phase p.1 p.2):ℂ)
  have hH : Integrable H (volume.prod planeMeasure) := by
    apply (hk.mul_prod hF).mul_bdd (c := 1)
    · exact (show Continuous (fun p : ℝ×(ℝ×ℝ) =>
        (Real.fourierChar (phase p.1 p.2) : ℂ)) by dsimp [phase]; fun_prop).aestronglyMeasurable
    · filter_upwards [] with p
      exact le_of_eq (Circle.norm_coe _)
  have hleft (t : ℝ) : k t*planarInverse F (x.1,x.2-t) =
      ∫ omega, H (t,omega) ∂planeMeasure := by
    rw [planarInverse, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with omega
    change k t*((Real.fourierChar (phase t omega):ℂ)*F omega)=_
    dsimp only [H]
    ring
  have hright (omega : ℝ×ℝ) : (∫ t, H (t,omega)) =
      Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (𝓕 k (omega.2)*F omega) := by
    rw [Real.fourier_eq]
    simp only [Real.inner_apply, Circle.smul_def, smul_eq_mul]
    rw [← integral_mul_const, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [H]
    have hp : phase t omega=(x.1*omega.1+x.2*omega.2)+(-(t*(omega.2))) := by
      dsimp [phase]
      ring
    rw [hp, Real.fourierChar.map_add_eq_mul]
    push_cast
    ring
  calc
    _ = ∫ t, ∫ omega, H (t,omega) ∂planeMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall hleft)
    _ = ∫ omega, (∫ t, H (t,omega) ∂volume) ∂planeMeasure := integral_integral_swap hH
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hright)


theorem schwartz_vertical_multiplier (K : ℝ → ℂ) (hK : Integrable K)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    verticalConvolution K f z=
      planarInverse (fun omega => 𝓕 K omega.2*planarFourier f omega) z := by
  have h := vertical_inverse_multiplier K (planarFourier f) hK (planarFourier_integrable f) z
  simpa only [funext (planarFourier_inversion f),planarInverse] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SchwartzVerticalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical frequency cutoffs preserve the actual planar Schwartz class. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem schwartzVerticalProjection_eq_convolution (q : SchwartzMap ℝ ℂ) (W center : ℝ)
    (hW : 0<W) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    schwartzVerticalProjection q W center f z=
      verticalConvolution (verticalProfileKernel q W center) f z := by
  rw [schwartz_vertical_multiplier (verticalProfileKernel q W center)
    (modulatedTimeKernel_integrable (𝓕⁻ q : SchwartzMap ℝ ℂ) W center hW)]
  simp_rw [verticalProfileKernel_fourier q W center _ hW]
  rw [schwartzVerticalProjection,planarInverseSchwartz_apply]
  congr 1
  funext omega
  rw [SchwartzMap.smulLeftCLM_apply_apply (verticalProfile_temperate q W center),
    planarFourierSchwartz_apply,smul_eq_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortSlopeOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short-time frozen-direction operator and the exact reason it may
replace the full kernel in a pairing on a narrow horizontal strip. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem shortSlopeOperator_pairing_eq (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (f g : (ℝ×ℝ) → ℂ) (l r : ℝ) (hwidth : r-l≤1/4)
    (hf : ∀ z, z.1∉Icc l r → f z=0) (hg : ∀ z, z.1∉Icc l r → g z=0)
    (z : ℝ×ℝ) :
    shortSlopeOperator K u f z*star (g z)=slopeKernelOperator K u f z*star (g z) := by
  by_cases hg0 : g z=0
  · simp only [hg0,star_zero,mul_zero]
  have hz : z.1∈Icc l r := by
    by_contra h
    exact hg0 (hg z h)
  unfold shortSlopeOperator slopeKernelOperator
  rw [←integral_mul_const,←integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : |t|≤1/4
  · simp only [ite_eq_left ht]
  · have hnot : z.1-t∉Icc l r := by
      intro h
      apply ht
      apply abs_le.mpr
      constructor <;> linarith [hz.1,hz.2,h.1,h.2]
    rw [ite_eq_right ht,hf _ hnot]
    simp only [mul_zero,zero_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortSlopeL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrable time-kernel errors have direct mass bounds under short
Lipschitz sampling, sufficient for restricted pairings. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem shortSlopeOperator_uniform (K : ℝ → ℂ) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ) (C : ℝ) (hC : 0≤C)
    (hf : ∀ z, ‖f z‖≤C) (z : ℝ×ℝ) :
    ‖shortSlopeOperator K u f z‖≤C*(∫ t, ‖K t‖) := by
  have h := norm_integral_le_of_norm_le (hK.norm.const_mul C)
    (Filter.Eventually.of_forall (fun t => show
      ‖if |t|≤1/4 then K t*f (z.1-t,z.2-t*u z) else 0‖≤C*‖K t‖ from by
      by_cases ht : |t|≤1/4
      · rw [ite_eq_left ht,norm_mul,mul_comm C]
        exact mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)
      · rw [ite_eq_right ht,norm_zero]
        exact mul_nonneg hC (norm_nonneg _)))
  simpa only [shortSlopeOperator,integral_const_mul] using h

theorem shortSlopeOperator_l1 (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hf : Integrable f planeMeasure) :
    Integrable (shortSlopeOperator K u f) planeMeasure ∧
      (∫ z, ‖shortSlopeOperator K u f z‖ ∂planeMeasure)≤
        4*(∫ t, ‖K t‖)*(∫ z, ‖f z‖ ∂planeMeasure) := by
  let F := fun p : ℝ×(ℝ×ℝ) =>
    if |p.1|≤1/4 then f (p.2.1-p.1,p.2.2-p.1*u p.2) else 0
  have hum := hu.continuous.measurable
  have hs : MeasurableSet {p : ℝ×(ℝ×ℝ) | |p.1|≤1/4} := by
    exact (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hFm : Measurable F := (hfm.comp (by fun_prop)).ite hs measurable_const
  have hslice (t : ℝ) : Integrable (fun z => ‖F (t,z)‖) planeMeasure ∧
      (∫ z, ‖F (t,z)‖ ∂planeMeasure)≤4*∫ z, ‖f z‖ ∂planeMeasure := by
    by_cases ht : |t|≤1/4
    · simpa only [F,ite_eq_left ht,Function.comp_def,verticalSampling,sub_zero] using
        planar_integral_comp_le_four (verticalSampling u t t 0)
          (verticalSampling_measurable u hum t t 0)
          (verticalSampling_antilipschitz u hu t t 0 ht) (fun z => ‖f z‖) hf.norm
          (fun _ => norm_nonneg _)
    · simp only [F,ite_eq_right ht,norm_zero,integral_zero]
      exact ⟨integrable_zero _ _ _,by positivity⟩
  let H := fun p : ℝ×(ℝ×ℝ) => K p.1*F p
  have hHm : Measurable H := (hKm.comp measurable_fst).mul hFm
  have hHi : Integrable H (volume.prod planeMeasure) := by
    apply (integrable_prod_iff hHm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun t =>
        ((hslice t).1.mono
          (hFm.comp (by fun_prop)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun _ => by simp)).const_mul (K t)
    · apply (hK.norm.mul_const (4*∫ z, ‖f z‖ ∂planeMeasure)).mono'
        hHm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards [] with t
      change ‖∫ z, ‖K t*F (t,z)‖ ∂planeMeasure‖≤_
      simp only [norm_mul,integral_const_mul]
      rw [Real.norm_of_nonneg (norm_nonneg _),
        Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hslice t).2 (norm_nonneg _)
  have heq (z : ℝ×ℝ) : (∫ t, H (t,z))=shortSlopeOperator K u f z := by
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [H,F]
    split_ifs <;> simp
  have hbound (z : ℝ×ℝ) : ‖shortSlopeOperator K u f z‖≤∫ t, ‖H (t,z)‖ := by
    rw [←heq]
    exact norm_integral_le_integral_norm _
  refine ⟨?_,?_⟩
  · simpa only [heq] using hHi.integral_prod_right
  · calc
      _ ≤ ∫ z : ℝ×ℝ, (∫ t : ℝ, ‖H (t,z)‖) ∂planeMeasure :=
        integral_mono (by simpa only [heq] using hHi.integral_prod_right.norm)
          hHi.norm.integral_prod_right hbound
      _ = ∫ t, ∫ z, ‖H (t,z)‖ ∂planeMeasure :=
        integral_integral_swap (f:=fun (z : ℝ×ℝ) (t : ℝ) => ‖H (t,z)‖) hHi.norm.swap
      _ ≤ ∫ t, ‖K t‖*(4*∫ z, ‖f z‖ ∂planeMeasure) := by
        apply integral_mono hHi.norm.integral_prod_left (hK.norm.mul_const _)
        intro t
        simp only [H,norm_mul,integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hslice t).2 (norm_nonneg _)
      _ = _ := by rw [integral_mul_const]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ShortKernelPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricted mass bounds for an integrable short-time kernel error. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem shortKernel_pairing (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f g : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f planeMeasure) (hg : Integrable g planeMeasure)
    (hf1 : ∀ z, ‖f z‖≤1) (hg1 : ∀ z, ‖g z‖≤1) :
    Integrable (fun z => shortSlopeOperator K u f z*star (g z)) planeMeasure ∧
    ‖∫ z, shortSlopeOperator K u f z*star (g z) ∂planeMeasure‖≤
      min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)*(∫ t, ‖K t‖) := by
  have hA := shortSlopeOperator_l1 K hKm hK u hu f hfm hf
  have hm := shortSlopeOperator_measurable K hKm u hu.continuous.measurable f hfm
  have hp (z : ℝ×ℝ) : ‖shortSlopeOperator K u f z*star (g z)‖≤‖shortSlopeOperator K u f z‖ := by
    rw [norm_mul,norm_star]
    exact mul_le_of_le_one_right (norm_nonneg _) (hg1 z)
  have hi := hA.1.norm.mono' (show Measurable (fun z => shortSlopeOperator K u f z*star (g z)) from by fun_prop).aestronglyMeasurable (Filter.Eventually.of_forall hp)
  refine ⟨hi,?_⟩
  rw [min_mul_of_nonneg _ _ (integral_nonneg fun _ => norm_nonneg _)]
  apply le_min
  · calc
      _ ≤ ∫ z, ‖shortSlopeOperator K u f z‖ ∂planeMeasure :=
        norm_integral_le_of_norm_le hA.1.norm (Filter.Eventually.of_forall hp)
      _ ≤ _ := hA.2.trans_eq (by ring)
  · have hp' (z : ℝ×ℝ) : ‖shortSlopeOperator K u f z*star (g z)‖≤
        (∫ t, ‖K t‖)*‖g z‖ := by
      rw [norm_mul,norm_star]
      have hb := shortSlopeOperator_uniform K hK u f 1 (by norm_num) hf1 z
      simp only [one_mul] at hb
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    have h := norm_integral_le_of_norm_le (hg.norm.const_mul (∫ t, ‖K t‖))
      (Filter.Eventually.of_forall hp')
    simpa only [integral_const_mul,integral_mul_const,mul_comm] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_KernelDifferencePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A kernel L1 error controls the actual localized bilinear form by the
smaller of the input and test masses. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem slopeOperator_kernel_sub (K J : ℝ → ℂ) (hK : Integrable K) (hJ : Integrable J)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    slopeKernelOperator (fun t => K t-J t) u f z=
      slopeKernelOperator K u f z-slopeKernelOperator J u f z := by
  simp only [slopeKernelOperator,sub_mul]
  exact integral_sub (slope_integrand_integrable K hK u f z)
    (slope_integrand_integrable J hJ u f z)

theorem shortSlopeOperator_kernel_sub (K J : ℝ → ℂ) (hK : Integrable K) (hJ : Integrable J)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    shortSlopeOperator (fun t => K t-J t) u f z=
      shortSlopeOperator K u f z-shortSlopeOperator J u f z := by
  simp only [shortSlopeOperator_eq_kernel]
  have heq : shortTimeKernel (fun t => K t-J t)=
      fun t => shortTimeKernel K t-shortTimeKernel J t := by
    funext t
    unfold shortTimeKernel
    split_ifs <;> simp
  rw [heq]
  exact slopeOperator_kernel_sub _ _ (shortTimeKernel_integrable K hK)
    (shortTimeKernel_integrable J hJ) u f z

theorem kernelDifference_pairing (K J : ℝ → ℂ) (hKm : Measurable K) (hJm : Measurable J)
    (hK : Integrable K) (hJ : Integrable J)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (hf1 : ∀ z, ‖f z‖≤1) (hg1 : ∀ z, ‖g z‖≤1)
    (l r : ℝ) (hwidth : r-l≤1/4)
    (hfstrip : ∀ z, z.1∉Icc l r → f z=0) (hgstrip : ∀ z, z.1∉Icc l r → g z=0) :
    ‖(∫ z, slopeKernelOperator K u f z*star (g z) ∂planeMeasure)-
      (∫ z, slopeKernelOperator J u f z*star (g z) ∂planeMeasure)‖≤
      min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)*
        (∫ t, ‖K t-J t‖) := by
  have hkp := shortKernel_pairing K hKm hK u hu f g f.continuous.measurable
    g.continuous.measurable f.integrable g.integrable hf1 hg1
  have hjp := shortKernel_pairing J hJm hJ u hu f g f.continuous.measurable
    g.continuous.measurable f.integrable g.integrable hf1 hg1
  have hdiff := shortKernel_pairing (fun t => K t-J t) (hKm.sub hJm) (hK.sub hJ) u hu
    f g f.continuous.measurable g.continuous.measurable f.integrable g.integrable hf1 hg1
  have heqK (z : ℝ×ℝ) := shortSlopeOperator_pairing_eq K u f g l r hwidth hfstrip hgstrip z
  have heqJ (z : ℝ×ℝ) := shortSlopeOperator_pairing_eq J u f g l r hwidth hfstrip hgstrip z
  simp_rw [←heqK,←heqJ]
  rw [←integral_sub hkp.1 hjp.1]
  have heq (z : ℝ×ℝ) : shortSlopeOperator K u f z*star (g z)-
      shortSlopeOperator J u f z*star (g z)=
        shortSlopeOperator (fun t => K t-J t) u f z*star (g z) := by
    rw [shortSlopeOperator_kernel_sub K J hK hJ]
    ring
  simpa only [heq] using hdiff.2

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_KernelPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability and kernel linearity of the actual scalar pairing. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem kernelPairing_smul (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (f g : SchwartzMap (ℝ×ℝ) ℂ) (c : ℂ) :
    kernelPairing K u (c • f) g=c*kernelPairing K u f g := by
  have heq (z : ℝ×ℝ) : slopeKernelOperator K u (c • f : SchwartzMap (ℝ×ℝ) ℂ) z=
      c*slopeKernelOperator K u f z := by
    unfold slopeKernelOperator
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [smul_apply,smul_eq_mul]
    ring
  simp only [kernelPairing,heq,mul_assoc]
  exact integral_const_mul _ _

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CompactMollification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive compact mollifiers preserve the unit bound and give actual
Schwartz approximants for compactly supported measurable tests. -/
noncomputable section
open MeasureTheory Function
open scoped Convolution Pointwise
namespace LipschitzHilbert.PacketRepresentation

theorem compactMollification_apply (phi : ContDiffBump (0 : ℝ×ℝ))
    (f : (ℝ×ℝ) → ℂ) (hf : Integrable f planeMeasure) (hc : HasCompactSupport f) (z : ℝ×ℝ) :
    compactMollification phi f hf hc z=
      ∫ t, phi.normed planeMeasure t • f (z-t) ∂planeMeasure := rfl

theorem compactMollification_unit (phi : ContDiffBump (0 : ℝ×ℝ))
    (f : (ℝ×ℝ) → ℂ) (hf : Integrable f planeMeasure) (hc : HasCompactSupport f)
    (hb : ∀ z, ‖f z‖≤1) : ∀ z, ‖compactMollification phi f hf hc z‖≤1 := by
  intro z
  rw [compactMollification_apply]
  have h := norm_integral_le_of_norm_le (phi.integrable_normed (μ:=planeMeasure))
    (Filter.Eventually.of_forall fun t => show
      ‖phi.normed planeMeasure t • f (z-t)‖≤phi.normed planeMeasure t from by
      rw [norm_smul,Real.norm_of_nonneg (phi.nonneg_normed _)]
      exact mul_le_of_le_one_right (phi.nonneg_normed _) (hb _))
  simpa only [phi.integral_normed] using h

theorem compactMollification_support (phi : ContDiffBump (0 : ℝ×ℝ))
    (f : (ℝ×ℝ) → ℂ) (hf : Integrable f planeMeasure) (hc : HasCompactSupport f) :
    support (compactMollification phi f hf hc)⊆
      Metric.ball 0 phi.rOut+support f := by
  change support (phi.normed planeMeasure ⋆[ContinuousLinearMap.lsmul ℝ ℝ,planeMeasure] f)⊆_
  rw [←phi.support_normed_eq (μ:=planeMeasure)]
  exact support_convolution_subset _

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CompactMollificationFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed shrinking positive mollifier family. Its a.e. convergence
comes from the existing Lebesgue differentiation theorem. -/
noncomputable section
open MeasureTheory Filter Function
open scoped Convolution Topology Pointwise
namespace LipschitzHilbert.PacketRepresentation

theorem testMollifier_radius_le_one (n : ℕ) : (testMollifier n).rOut≤1 := by
  change 1/((n:ℝ)+1)≤1
  exact (div_le_one (by positivity)).2 (by linarith [Nat.cast_nonneg (α:=ℝ) n])

theorem testMollifier_radius_tendsto :
    Tendsto (fun n => (testMollifier n).rOut) atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem compactMollification_ae_tendsto (f : (ℝ×ℝ) → ℂ)
    (hf : Integrable f planeMeasure) (hc : HasCompactSupport f) :
    ∀ᵐ z ∂planeMeasure, Tendsto (fun n => compactMollification (testMollifier n) f hf hc z)
      atTop (nhds (f z)) := by
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    testMollifier_radius_tendsto
    (Filter.Eventually.of_forall fun n => show (testMollifier n).rOut≤2*(testMollifier n).rIn from by
      change 1/((n:ℝ)+1)≤2*((1/((n:ℝ)+1))/2)
      linarith) hf.locallyIntegrable

theorem compactMollification_common_support (f : (ℝ×ℝ) → ℂ)
    (hf : Integrable f planeMeasure) (hc : HasCompactSupport f) (n : ℕ) :
    support (compactMollification (testMollifier n) f hf hc)⊆
      Metric.closedBall (0 : ℝ×ℝ) 1+tsupport f := by
  apply (compactMollification_support _ f hf hc).trans
  apply Set.add_subset_add _ subset_closure
  exact (Metric.ball_subset_ball (testMollifier_radius_le_one n)).trans Metric.ball_subset_closedBall

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CompactMollificationL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive compact mollification converges in L2 for bounded compact
measurable tests, with a common compact support. -/
noncomputable section
open MeasureTheory Function Set Filter
open scoped Topology Convolution Pointwise
namespace LipschitzHilbert.PacketRepresentation

theorem compactMollification_energy_tendsto (f : (ℝ×ℝ) → ℂ)
    (hfm : Measurable f) (hf : Integrable f planeMeasure) (hc : HasCompactSupport f)
    (hb : ∀ z, ‖f z‖≤1) :
    Tendsto (fun n => ∫ z, ‖compactMollification (testMollifier n) f hf hc z-f z‖^2 ∂planeMeasure)
      atTop (nhds 0) := by
  let S := Metric.closedBall (0 : ℝ×ℝ) 1+tsupport f
  have hS : IsCompact S := (isCompact_closedBall _ _).add hc
  have hfs : support f⊆S := by
    intro z hz
    exact Set.mem_add.mpr ⟨0,by simp,z,subset_closure hz,zero_add z⟩
  have hgs (n : ℕ) : support (compactMollification (testMollifier n) f hf hc)⊆S :=
    compactMollification_common_support f hf hc n
  have hdom : Integrable (S.indicator (fun _ => (4:ℝ))) planeMeasure :=
    (integrableOn_const hS.measure_lt_top.ne).integrable_indicator hS.measurableSet
  have h := tendsto_integral_of_dominated_convergence (μ:=planeMeasure)
    (S.indicator (fun _ => (4:ℝ)))
    (F:=fun n z => ‖compactMollification (testMollifier n) f hf hc z-f z‖^2) (f:=fun _ => (0:ℝ))
    (fun n => (((compactMollification (testMollifier n) f hf hc).continuous.measurable.sub hfm).norm.pow_const 2).aestronglyMeasurable)
    hdom (fun n => Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      by_cases hz : z∈S
      · rw [Set.indicator_of_mem hz]
        have hn : ‖compactMollification (testMollifier n) f hf hc z-f z‖≤2 :=
          (norm_sub_le _ _).trans (by linarith only [compactMollification_unit (testMollifier n) f hf hc hb z,hb z])
        simpa only [show (2:ℝ)^2=4 by norm_num] using pow_le_pow_left₀ (norm_nonneg _) hn 2
      · have hfz : f z=0 := notMem_support.mp (fun h => hz (hfs h))
        have hgz : compactMollification (testMollifier n) f hf hc z=0 :=
          notMem_support.mp (fun h => hz (hgs n h))
        simp only [Set.indicator_of_notMem hz,hfz,hgz,sub_self,norm_zero,zero_pow (by decide : 2≠0),le_refl])
    (by
      filter_upwards [compactMollification_ae_tendsto f hf hc] with z hz
      simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0)] using (hz.sub_const (f z)).norm.pow 2)
  simpa only [integral_zero] using h

theorem compactMollification_Lp_tendsto (f : (ℝ×ℝ) → ℂ)
    (hfm : Measurable f) (hf : Integrable f planeMeasure) (hc : HasCompactSupport f)
    (hb : ∀ z, ‖f z‖≤1) (hf2 : MemLp f 2 planeMeasure) :
    Tendsto (fun n => (compactMollification (testMollifier n) f hf hc).toLp 2 planeMeasure)
      atTop (nhds (hf2.toLp f)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n => compactMollification (testMollifier n) f hf hc)
    (fun n => (compactMollification (testMollifier n) f hf hc).memLp 2 planeMeasure) f hf2).mpr
  have he (n : ℕ) : eLpNorm ((compactMollification (testMollifier n) f hf hc : (ℝ×ℝ) → ℂ)-f) 2 planeMeasure=
      ENNReal.ofReal (Real.sqrt (∫ z, ‖compactMollification (testMollifier n) f hf hc z-f z‖^2 ∂planeMeasure)) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      (((compactMollification (testMollifier n) f hf hc).memLp 2 planeMeasure).sub hf2)]
    norm_num [Real.sqrt_eq_rpow]
  simp_rw [he]
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_sqrt.continuousAt.tendsto.comp (compactMollification_energy_tendsto f hfm hf hc hb))
  simpa only [Function.comp_def,Real.sqrt_zero,ENNReal.ofReal_zero] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CompactMollificationSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shrinking compact mollifiers eventually stay inside any prescribed
open neighbourhood of the original compact support. -/
noncomputable section
open MeasureTheory Function Set Filter
open scoped Topology Pointwise
namespace LipschitzHilbert.PacketRepresentation

theorem compactMollification_eventually_supported (f : (ℝ×ℝ) → ℂ)
    (hf : Integrable f planeMeasure) (hc : HasCompactSupport f)
    (K U : Set (ℝ×ℝ)) (hK : IsCompact K) (hfk : support f⊆K)
    (hU : IsOpen U) (hKU : K⊆U) :
    ∀ᶠ n : ℕ in atTop, support (compactMollification (testMollifier n) f hf hc)⊆U := by
  obtain ⟨V,hV,hVU⟩ := compact_open_separated_add_left hK hU hKU
  obtain ⟨delta,hdelta,hball⟩ := Metric.mem_nhds_iff.mp hV
  filter_upwards [testMollifier_radius_tendsto.eventually (gt_mem_nhds hdelta)] with n hn
  exact (compactMollification_support _ f hf hc).trans
    ((Set.add_subset_add ((Metric.ball_subset_ball hn.le).trans hball) hfk).trans hVU)

theorem exists_schwartz_approx_compact (f : (ℝ×ℝ) → ℂ)
    (hfm : Measurable f) (hf : Integrable f planeMeasure) (hc : HasCompactSupport f)
    (hb : ∀ z, ‖f z‖≤1) (hf2 : MemLp f 2 planeMeasure)
    (K U : Set (ℝ×ℝ)) (hK : IsCompact K) (hfk : support f⊆K)
    (hU : IsOpen U) (hKU : K⊆U) (epsilon : ℝ) (he : 0<epsilon) :
    ∃ g : SchwartzMap (ℝ×ℝ) ℂ, (∀ z, ‖g z‖≤1) ∧ support g⊆U ∧
      ‖g.toLp 2 planeMeasure-hf2.toLp f‖<epsilon := by
  have hlim := compactMollification_Lp_tendsto f hfm hf hc hb hf2
  have hclose := hlim.eventually (Metric.ball_mem_nhds _ he)
  obtain ⟨n,hn,hns⟩ := (hclose.and (compactMollification_eventually_supported f hf hc K U hK hfk hU hKU)).exists
  refine ⟨compactMollification (testMollifier n) f hf hc,compactMollification_unit _ f hf hc hb,hns,?_⟩
  simpa only [dist_eq_norm] using Metric.mem_ball.mp hn

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HilbertCutoffProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed smooth annular Hilbert multiplier and its cutoff derivative.
All profiles are constructed, rather than supplied as analytic inputs. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertSmoothSign_pos (x : ℝ) (hx : 1/2≤x) : hilbertSmoothSign x=1 := by
  simp [hilbertSmoothSign,Real.smoothTransition.one_of_one_le (show 1≤2*x+1 by linarith),
    Real.smoothTransition.zero_of_nonpos (show 1-2*x≤0 by linarith)]

theorem hilbertSmoothSign_neg (x : ℝ) (hx : x≤-(1/2)) : hilbertSmoothSign x= -1 := by
  simp [hilbertSmoothSign,Real.smoothTransition.zero_of_nonpos (show 2*x+1≤0 by linarith),
    Real.smoothTransition.one_of_one_le (show 1≤1-2*x by linarith)]

theorem hilbertSmoothSign_range (x : ℝ) : -1≤hilbertSmoothSign x ∧ hilbertSmoothSign x≤1 := by
  unfold hilbertSmoothSign
  constructor <;> linarith [Real.smoothTransition.nonneg (2*x+1),
    Real.smoothTransition.le_one (2*x+1),Real.smoothTransition.nonneg (1-2*x),
    Real.smoothTransition.le_one (1-2*x)]

theorem hilbertSmoothSign_deriv_zero (x : ℝ) (hx : 1/2≤|x|) :
    deriv hilbertSmoothSign x=0 := by
  rcases le_abs.mp hx with hx | hx
  · apply IsLocalMax.deriv_eq_zero
    apply Filter.Eventually.of_forall
    intro y
    rw [hilbertSmoothSign_pos x hx]
    exact (hilbertSmoothSign_range y).2
  · apply IsLocalMin.deriv_eq_zero
    apply Filter.Eventually.of_forall
    intro y
    rw [hilbertSmoothSign_neg x (by linarith)]
    exact (hilbertSmoothSign_range y).1

theorem hilbertAnnularSymbol_support (x : ℝ) (hx : hilbertAnnularSymbol x≠0) :
    1/2≤|x| ∧ |x|≤2 := by
  constructor
  · by_contra hn
    have ha := (lt_of_not_ge hn).le
    have ha1 : |x|≤1 := by linarith
    have ha2 : |2*x|≤1 := by rw [abs_mul]; norm_num; linarith
    apply hx
    change -(Real.pi:ℂ)*Complex.I*↑(hilbertSmoothSign x*
      (verticalBinPlateauReal x-verticalBinPlateauReal (2*x)))=0
    rw [verticalBinPlateauReal_one x ha1,verticalBinPlateauReal_one (2*x) ha2]
    simp
  · by_contra hn
    have ha : 2≤|x| := (lt_of_not_ge hn).le
    have hz (s : ℝ) (hs : 2≤|s|) : verticalBinPlateauReal s=0 := by
      apply verticalBinPlateauReal_zero
      rcases le_abs.mp hs with hs | hs
      · exact Or.inr hs
      · exact Or.inl (by linarith)
    have ha2 : 2≤|2*x| := by rw [abs_mul]; norm_num; linarith
    apply hx
    change -(Real.pi:ℂ)*Complex.I*↑(hilbertSmoothSign x*
      (verticalBinPlateauReal x-verticalBinPlateauReal (2*x)))=0
    rw [hz x ha,hz (2*x) ha2]
    simp

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HilbertCutoffDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating the actual annular multiplier gives a dyadic difference
of a single compactly supported smooth profile. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertSign_deriv_plateau (x : ℝ) : deriv hilbertSmoothSign x*
    (verticalBinPlateauReal x-verticalBinPlateauReal (2*x))=0 := by
  by_cases hx : |x|≤1/2
  · have hx1 : |x|≤1 := by linarith
    have hx2 : |2*x|≤1 := by rw [abs_mul]; norm_num; linarith
    rw [verticalBinPlateauReal_one x hx1,verticalBinPlateauReal_one (2*x) hx2]
    ring
  · rw [hilbertSmoothSign_deriv_zero x (le_of_lt (lt_of_not_ge hx)),zero_mul]

theorem hilbertSign_dilation_deriv (x : ℝ) :
    hilbertSmoothSign x*deriv verticalBinPlateauReal (2*x)=
      hilbertSmoothSign (2*x)*deriv verticalBinPlateauReal (2*x) := by
  by_cases hx : |x|≤1/2
  · have hx2 : |2*x|≤1 := by rw [abs_mul]; norm_num; linarith
    rw [verticalBinPlateauReal_deriv_zero (2*x) (Or.inl hx2)]
    ring
  · have hxabs : 1/2≤|x| := le_of_lt (lt_of_not_ge hx)
    rcases le_abs.mp hxabs with hp | hn
    · rw [hilbertSmoothSign_pos x hp,hilbertSmoothSign_pos (2*x) (by linarith)]
    · rw [hilbertSmoothSign_neg x (by linarith),hilbertSmoothSign_neg (2*x) (by linarith)]

theorem hilbertAnnularSymbol_hasDerivAt (x : ℝ) :
    HasDerivAt hilbertAnnularSymbol
      (-(Real.pi:ℂ)*Complex.I*(hilbertCutoffDerivative x-2*hilbertCutoffDerivative (2*x))) x := by
  have hs := ((contDiff_infty_iff_deriv.mp hilbertSmoothSign_smooth).1 x).hasDerivAt
  have hc (s : ℝ) := ((contDiff_infty_iff_deriv.mp verticalBinPlateauReal_smooth).1 s).hasDerivAt
  have hc2 := (hc (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hd := (hs.mul ((hc x).sub hc2)).ofReal_comp.const_mul (-(Real.pi:ℂ)*Complex.I)
  refine hd.congr_deriv ?_
  · symm
    change -(Real.pi:ℂ)*Complex.I*
      (↑(hilbertSmoothSign x*deriv verticalBinPlateauReal x)-
        2*↑(hilbertSmoothSign (2*x)*deriv verticalBinPlateauReal (2*x))) = _
    simp only [Pi.sub_apply,Function.comp_apply]
    rw [hilbertSign_deriv_plateau,zero_add]
    have heq : hilbertSmoothSign x*(deriv verticalBinPlateauReal x-
        deriv verticalBinPlateauReal (2*x)*(2*1))=
        hilbertSmoothSign x*deriv verticalBinPlateauReal x-
          2*(hilbertSmoothSign (2*x)*deriv verticalBinPlateauReal (2*x)) := by
      rw [←hilbertSign_dilation_deriv]
      ring
    rw [heq]
    push_cast
    ring

theorem hilbertAnnularSymbol_deriv (x : ℝ) :
    deriv hilbertAnnularSymbol x=
      -(Real.pi:ℂ)*Complex.I*(hilbertCutoffDerivative x-2*hilbertCutoffDerivative (2*x)) :=
  (hilbertAnnularSymbol_hasDerivAt x).deriv

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HilbertCutoffNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact derivative profile has integral minus two, fixing the
normalization of the physical telescoping profile at the origin. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertCutoffDerivative_nonneg_arg (x : ℝ) (hx : 0≤x) :
    hilbertCutoffDerivative x=((deriv verticalBinPlateauReal x : ℝ) : ℂ) := by
  change ((hilbertSmoothSign x*deriv verticalBinPlateauReal x : ℝ) : ℂ)=_
  by_cases h : 1/2≤x
  · rw [hilbertSmoothSign_pos x h,one_mul]
  · have ha : |x|≤1 := by rw [abs_of_nonneg hx]; linarith
    rw [verticalBinPlateauReal_deriv_zero x (Or.inl ha),mul_zero,Complex.ofReal_zero]

theorem hilbertCutoffDerivative_nonpos_arg (x : ℝ) (hx : x≤0) :
    hilbertCutoffDerivative x= -((deriv verticalBinPlateauReal x : ℝ) : ℂ) := by
  change ((hilbertSmoothSign x*deriv verticalBinPlateauReal x : ℝ) : ℂ)=_
  by_cases h : x≤-(1/2)
  · rw [hilbertSmoothSign_neg x h,neg_one_mul,Complex.ofReal_neg]
  · have ha : |x|≤1 := by rw [abs_of_nonpos hx]; linarith
    rw [verticalBinPlateauReal_deriv_zero x (Or.inl ha),mul_zero,Complex.ofReal_zero,neg_zero]

theorem hilbertCutoffDerivative_integral : (∫ x, hilbertCutoffDerivative x)=(-2:ℂ) := by
  have hc : Continuous (fun x => ((deriv verticalBinPlateauReal x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (contDiff_infty_iff_deriv.mp verticalBinPlateauReal_smooth).2.continuous
  have hd (x : ℝ) : HasDerivAt verticalBinPlateau ((deriv verticalBinPlateauReal x : ℝ) : ℂ) x := by
    exact ((contDiff_infty_iff_deriv.mp verticalBinPlateauReal_smooth).1 x).hasDerivAt.ofReal_comp
  have hpos : (∫ x in (0:ℝ)..3, hilbertCutoffDerivative x)=(-1:ℂ) := by
    calc
      _ = ∫ x in (0:ℝ)..3, ((deriv verticalBinPlateauReal x : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (0:ℝ)≤3)] at hx
        exact hilbertCutoffDerivative_nonneg_arg x hx.1
      _ = verticalBinPlateau 3-verticalBinPlateau 0 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable _ _)
      _ = -1 := by
        have h3 : verticalBinPlateau (3:ℝ)=0 := by
          change (verticalBinPlateauReal 3:ℂ)=0
          rw [verticalBinPlateauReal_zero 3 (Or.inr (by norm_num)),Complex.ofReal_zero]
        rw [h3,verticalBinPlateau_one 0 (by norm_num),zero_sub]
  have hneg : (∫ x in (-3:ℝ)..0, hilbertCutoffDerivative x)=(-1:ℂ) := by
    calc
      _ = ∫ x in (-3:ℝ)..0, -((deriv verticalBinPlateauReal x : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (-3:ℝ)≤0)] at hx
        exact hilbertCutoffDerivative_nonpos_arg x hx.2
      _ = -(verticalBinPlateau 0-verticalBinPlateau (-3)) := by
        rw [intervalIntegral.integral_neg]
        congr 1
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable _ _)
      _ = -1 := by
        have h3 : verticalBinPlateau (-3:ℝ)=0 := by
          change (verticalBinPlateauReal (-3):ℂ)=0
          rw [verticalBinPlateauReal_zero (-3) (Or.inl (by norm_num)),Complex.ofReal_zero]
        rw [h3,verticalBinPlateau_one 0 (by norm_num),sub_zero]
  have hsupport : Function.support hilbertCutoffDerivative ⊆ Ioc (-3:ℝ) 3 := by
    intro x hx
    have ha : |x|<2 := by
      by_contra hn
      have hz := verticalBinPlateauReal_deriv_zero x (Or.inr (le_of_not_gt hn))
      apply hx
      change ((hilbertSmoothSign x*deriv verticalBinPlateauReal x : ℝ) : ℂ)=0
      rw [hz,mul_zero,Complex.ofReal_zero]
    have hb := abs_lt.mp ha
    constructor <;> linarith
  rw [←intervalIntegral.integral_eq_integral_of_support_subset hsupport,
    ←intervalIntegral.integral_add_adjacent_intervals
      (hilbertCutoffDerivative.continuous.intervalIntegrable (-3) 0)
      (hilbertCutoffDerivative.continuous.intervalIntegrable 0 3),hneg,hpos]
  norm_num

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TimeErrorEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A normalized integrable envelope for the two endpoint errors in a
sharp time truncation. Its integral is independent of its radius. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem timeErrorEnvelope_nonneg (r t : ℝ) (hr : 0 < r) : 0≤timeErrorEnvelope r t := by
  unfold timeErrorEnvelope
  positivity

theorem timeErrorEnvelope_eq (r t : ℝ) (hr : 0 < r) :
    timeErrorEnvelope r t=r⁻¹*lineEnvelope 0 r 1 t := by
  unfold timeErrorEnvelope lineEnvelope
  simp only [sub_zero,pow_one]
  have hden : r^2+t^2≠0 := ne_of_gt (by positivity)
  have hden' : 1+(t/r)^2≠0 := ne_of_gt (by positivity)
  field_simp

theorem timeErrorEnvelope_integrable (r : ℝ) (hr : 0 < r) :
    Integrable (timeErrorEnvelope r) := by
  have h := (integrable_lineEnvelope_one 0 r hr).const_mul r⁻¹
  simpa only [←timeErrorEnvelope_eq r _ hr] using h

theorem timeErrorEnvelope_integral (r : ℝ) (hr : 0 < r) :
    (∫ t, timeErrorEnvelope r t)=Real.pi := by
  simp_rw [timeErrorEnvelope_eq r _ hr]
  rw [integral_const_mul,integral_lineEnvelope_one 0 r hr]
  field_simp

theorem timeErrorEnvelope_small (r t : ℝ) (hr : 0 < r) (ht : |t| ≤ r) :
    r⁻¹≤2*timeErrorEnvelope r t := by
  have ht2 : t^2 ≤ r^2 := by nlinarith [sq_abs t,pow_le_pow_left₀ (abs_nonneg t) ht 2]
  have hd : 0 < r^2+t^2 := by positivity
  unfold timeErrorEnvelope
  rw [←mul_div_assoc]
  apply (le_div_iff₀ hd).2
  rw [inv_mul_eq_div]
  apply (div_le_iff₀ hr).2
  nlinarith

theorem timeErrorEnvelope_large (r t : ℝ) (hr : 0 < r) (ht : r≤|t|) :
    r/t^2≤2*timeErrorEnvelope r t := by
  have ht2 : r^2≤t^2 := by nlinarith [sq_abs t,pow_le_pow_left₀ hr.le ht 2]
  have hd : 0 < r^2+t^2 := by positivity
  have htpos : 0<t^2 := lt_of_lt_of_le (sq_pos_of_pos hr) ht2
  unfold timeErrorEnvelope
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ htpos hd).2
  nlinarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicKernelTelescoping
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact telescoping identity behind the finite Hilbert time-kernel
decomposition. The cutoff profile will be constructed independently. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem finiteTimeKernel_telescope (k : SchwartzMap ℝ ℂ) (a : ℝ → ℂ)
    (hprofile : ∀ s : ℝ, (s : ℂ)*k s=a s-a (s/2))
    (N : ℕ) (topLength : ℝ) (htop : 0<topLength) (t : ℝ) :
    (t : ℂ)*finiteTimeKernel k N topLength t=
      a ((2:ℝ)^N*t/(2*topLength))-a (t/(2*topLength)) := by
  have hterm (j : Fin N) : (t : ℂ)*scaledTimeKernel k (topLength/(2:ℝ)^j.val) t=
      a ((2:ℝ)^(j.val+1)*t/(2*topLength))-a ((2:ℝ)^j.val*t/(2*topLength)) := by
    have hl : 0<topLength/(2:ℝ)^j.val := div_pos htop (pow_pos (by norm_num) _)
    have heq : (t : ℂ)*scaledTimeKernel k (topLength/(2:ℝ)^j.val) t=
        ((t/(topLength/(2:ℝ)^j.val) : ℝ) : ℂ)*k (t/(topLength/(2:ℝ)^j.val)) := by
      unfold scaledTimeKernel
      push_cast
      ring
    rw [heq,hprofile]
    have harg : t/(topLength/(2:ℝ)^j.val)=(2:ℝ)^(j.val+1)*t/(2*topLength) := by
      rw [pow_succ]
      field_simp
    have hhalf : (t/(topLength/(2:ℝ)^j.val))/2=(2:ℝ)^j.val*t/(2*topLength) := by
      field_simp
    rw [harg]
    congr 1
    rw [←harg,hhalf]
  unfold finiteTimeKernel
  rw [Finset.mul_sum]
  simp_rw [hterm]
  change (∑ j : Fin N, (fun n : ℕ =>
    a ((2:ℝ)^(n+1)*t/(2*topLength))-a ((2:ℝ)^n*t/(2*topLength))) j.val)=_
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ =>
    a ((2:ℝ)^(n+1)*t/(2*topLength))-a ((2:ℝ)^n*t/(2*topLength))) N]
  simpa only [pow_zero,one_mul] using
    Finset.sum_range_sub (fun n : ℕ => a ((2:ℝ)^n*t/(2*topLength))) N

theorem finiteTimeKernel_eq_profileDifference (k : SchwartzMap ℝ ℂ) (a : ℝ → ℂ)
    (hprofile : ∀ s : ℝ, (s : ℂ)*k s=a s-a (s/2))
    (N : ℕ) (topLength : ℝ) (htop : 0<topLength) (t : ℝ) (ht : t≠0) :
    finiteTimeKernel k N topLength t=
      profileKernelDifference a (2*topLength/(2:ℝ)^N) (2*topLength) t := by
  have h := finiteTimeKernel_telescope k a hprofile N topLength htop t
  have harg : t/(2*topLength/(2:ℝ)^N)=(2:ℝ)^N*t/(2*topLength) := by field_simp
  unfold profileKernelDifference
  rw [harg]
  apply (eq_div_iff (by exact_mod_cast ht : (t:ℂ)≠0)).2
  simpa only [mul_comm] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SharpKernelComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two endpoint envelopes control sharp truncation versus a telescoped
kernel. The profile conditions are local construction obligations. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem profile_far_bound (a : ℝ → ℂ) (D : ℝ)
    (hfar : ∀ s, |s| *‖a s‖≤D) (r t : ℝ) (hr : 0 < r) (ht : t≠0) :
    ‖a (t/r)‖≤D*r/|t| := by
  have hf : ‖a (t/r)‖*|t|/r≤D := by
    simpa only [abs_div,abs_of_pos hr,div_mul_eq_mul_div,mul_comm] using hfar (t/r)
  apply (le_div_iff₀ (abs_pos.mpr ht)).2
  exact (div_le_iff₀ hr).1 hf

theorem sharpKernelComparison_pointwise (a : ℝ → ℂ) (D : ℝ) (hD : 0≤D)
    (hnear : ∀ s, ‖a s+1‖≤D*|s|) (hfar : ∀ s, |s| *‖a s‖≤D)
    (r R : ℝ) (hr : 0 < r) (hrR : r≤R) (t : ℝ) :
    ‖sharpTimeKernel r R t-profileKernelDifference a r R t‖≤
      4*D*(timeErrorEnvelope r t+timeErrorEnvelope R t) := by
  have hR : 0<R := hr.trans_le hrR
  have hqr := timeErrorEnvelope_nonneg r t hr
  have hqR := timeErrorEnvelope_nonneg R t hR
  by_cases ht0 : t=0
  · subst t
    have hs : ¬(r < |(0:ℝ)| ∧ |(0:ℝ)| < R) := by simp [not_lt_of_ge hr.le]
    simp only [sharpTimeKernel,ite_eq_right hs,profileKernelDifference,
      Complex.ofReal_zero,div_zero,sub_zero,norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) hD) (add_nonneg hqr hqR)
  have ht : 0 < |t| := abs_pos.mpr ht0
  have hnear_r : ‖a (t/r)+1‖≤D*(|t|/r) := by
    simpa only [abs_div,abs_of_pos hr] using hnear (t/r)
  have hnear_R : ‖a (t/R)+1‖≤D*(|t|/R) := by
    simpa only [abs_div,abs_of_pos hR] using hnear (t/R)
  have hfar_r := profile_far_bound a D hfar r t hr ht0
  have hfar_R := profile_far_bound a D hfar R t hR ht0
  by_cases hlo : |t| ≤ r
  · have hs : ¬(r < |t| ∧ |t| < R) := by intro h; linarith [h.1]
    have hnum : ‖a (t/r)-a (t/R)‖≤2*D*|t|/r := by
      have hn := norm_sub_le (a (t/r)+1) (a (t/R)+1)
      have hdiff : (a (t/r)+1)-(a (t/R)+1)=a (t/r)-a (t/R) := by ring
      rw [hdiff] at hn
      have hdiv := div_le_div_of_nonneg_left ht.le hr hrR
      calc
        _ ≤ D*(|t|/r)+D*(|t|/r) := hn.trans
          (add_le_add hnear_r (hnear_R.trans (mul_le_mul_of_nonneg_left hdiv hD)))
        _ = _ := by ring
    calc
      _ = ‖a (t/r)-a (t/R)‖/|t| := by
        simp only [sharpTimeKernel,ite_eq_right hs,profileKernelDifference,zero_sub,norm_neg,
          norm_div,Complex.norm_real,Real.norm_eq_abs]
      _ ≤ (2*D*|t|/r)/|t| := div_le_div_of_nonneg_right hnum ht.le
      _ = 2*D*r⁻¹ := by field_simp
      _ ≤ 4*D*timeErrorEnvelope r t := by
        have h := mul_le_mul_of_nonneg_left (timeErrorEnvelope_small r t hr hlo) (mul_nonneg (by norm_num : (0:ℝ)≤2) hD)
        nlinarith only [h]
      _ ≤ _ := by nlinarith only [mul_nonneg hD hqR]
  · have htr : r < |t| := lt_of_not_ge hlo
    by_cases hhi : |t| < R
    · have hnum : ‖1-a (t/r)+a (t/R)‖≤D*r/|t|+D*(|t|/R) := by
        have heq : (1:ℂ)-a (t/r)+a (t/R)=(-a (t/r))+(a (t/R)+1) := by ring
        rw [heq]
        exact (norm_add_le _ _).trans (add_le_add (by simpa only [norm_neg] using hfar_r) hnear_R)
      have hform : sharpTimeKernel r R t-profileKernelDifference a r R t=
          ((1:ℂ)-a (t/r)+a (t/R))/(t : ℂ) := by
        have hs : r < |t| ∧ |t| < R := ⟨htr,hhi⟩
        simp only [sharpTimeKernel,ite_eq_left hs,profileKernelDifference]
        field_simp
        ring
      calc
        _ = ‖1-a (t/r)+a (t/R)‖/|t| := by rw [hform,norm_div,Complex.norm_real,Real.norm_eq_abs]
        _ ≤ (D*r/|t|+D*(|t|/R))/|t| := div_le_div_of_nonneg_right hnum ht.le
        _ = D*(r/t^2)+D*R⁻¹ := by rw [←sq_abs t]; field_simp
        _ ≤ 2*D*timeErrorEnvelope r t+2*D*timeErrorEnvelope R t := by
          have hrb := mul_le_mul_of_nonneg_left (timeErrorEnvelope_large r t hr htr.le) hD
          have hRb := mul_le_mul_of_nonneg_left (timeErrorEnvelope_small R t hR hhi.le) hD
          nlinarith only [hrb,hRb]
        _ ≤ _ := by nlinarith only [mul_nonneg hD hqr,mul_nonneg hD hqR]
    · have hs : ¬(r < |t| ∧ |t| < R) := by intro h; exact hhi h.2
      have hnum : ‖a (t/r)-a (t/R)‖≤2*D*R/|t| := by
        have h := (norm_sub_le _ _).trans (add_le_add hfar_r hfar_R)
        have hmon := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrR hD) ht.le
        calc
          _ ≤ D*R/|t|+D*R/|t| := h.trans (add_le_add hmon (le_refl _))
          _ = _ := by ring
      calc
        _ = ‖a (t/r)-a (t/R)‖/|t| := by
          simp only [sharpTimeKernel,ite_eq_right hs,profileKernelDifference,zero_sub,norm_neg,
            norm_div,Complex.norm_real,Real.norm_eq_abs]
        _ ≤ (2*D*R/|t|)/|t| := div_le_div_of_nonneg_right hnum ht.le
        _ = 2*D*(R/t^2) := by rw [←sq_abs t]; field_simp
        _ ≤ 4*D*timeErrorEnvelope R t := by
          have h := mul_le_mul_of_nonneg_left
            (timeErrorEnvelope_large R t hR (le_of_not_gt hhi)) (mul_nonneg (by norm_num : (0:ℝ)≤2) hD)
          nlinarith only [h]
        _ ≤ _ := by nlinarith only [mul_nonneg hD hqr]

end LipschitzHilbert.PacketRepresentation

namespace LipschitzHilbert.PacketRepresentation

theorem sharpKernelComparison_integral (a : ℝ → ℂ) (ha : Measurable a)
    (D : ℝ) (hD : 0≤D) (hnear : ∀ s, ‖a s+1‖≤D*|s|)
    (hfar : ∀ s, |s| *‖a s‖≤D) (r R : ℝ) (hr : 0 < r) (hrR : r≤R) :
    Integrable (fun t => sharpTimeKernel r R t-profileKernelDifference a r R t) ∧
      (∫ t, ‖sharpTimeKernel r R t-profileKernelDifference a r R t‖)≤8*Real.pi*D := by
  have hR := hr.trans_le hrR
  have hi := ((timeErrorEnvelope_integrable r hr).add
    (timeErrorEnvelope_integrable R hR)).const_mul (4*D)
  have hm : Measurable (fun t => sharpTimeKernel r R t-profileKernelDifference a r R t) := by
    apply (sharpTimeKernel_measurable r R).sub
    unfold profileKernelDifference
    exact ((ha.comp (by fun_prop)).sub (ha.comp (by fun_prop))).div (by fun_prop)
  have hb (t : ℝ) := sharpKernelComparison_pointwise a D hD hnear hfar r R hr hrR t
  have he := hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨he,?_⟩
  calc
    _ ≤ ∫ t, 4*D*(timeErrorEnvelope r t+timeErrorEnvelope R t) :=
      integral_mono he.norm hi hb
    _ = 8*Real.pi*D := by
      rw [integral_const_mul,integral_add (timeErrorEnvelope_integrable r hr)
        (timeErrorEnvelope_integrable R hR),timeErrorEnvelope_integral r hr,
        timeErrorEnvelope_integral R hR]
      ring

theorem finiteTimeKernel_sharp_integral (k : SchwartzMap ℝ ℂ) (a : ℝ → ℂ)
    (ha : Measurable a) (hprofile : ∀ s : ℝ, (s : ℂ)*k s=a s-a (s/2))
    (D : ℝ) (hD : 0≤D) (hnear : ∀ s, ‖a s+1‖≤D*|s|)
    (hfar : ∀ s, |s| *‖a s‖≤D) (N : ℕ) (topLength : ℝ) (htop : 0<topLength) :
    Integrable (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
      finiteTimeKernel k N topLength t) ∧
    (∫ t, ‖sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
      finiteTimeKernel k N topLength t‖)≤8*Real.pi*D := by
  have hr : 0<2*topLength/(2:ℝ)^N := by positivity
  have hrR : 2*topLength/(2:ℝ)^N≤2*topLength := by
    apply div_le_self (by positivity)
    exact one_le_pow₀ (by norm_num)
  have heq : (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
      finiteTimeKernel k N topLength t) =ᵐ[volume]
      (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        profileKernelDifference a (2*topLength/(2:ℝ)^N) (2*topLength) t) := by
    filter_upwards [volume.ae_ne (0:ℝ)] with t ht
    rw [finiteTimeKernel_eq_profileDifference k a hprofile N topLength htop t ht]
  obtain ⟨hi,hbound⟩ := sharpKernelComparison_integral a ha D hD hnear hfar _ _ hr hrR
  refine ⟨hi.congr heq.symm,?_⟩
  calc
    _ = ∫ t, ‖sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        profileKernelDifference a (2*topLength/(2:ℝ)^N) (2*topLength) t‖ :=
      integral_congr_ae (heq.mono fun _ h => congrArg norm h)
    _ ≤ _ := hbound

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SchwartzProfileBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The endpoint assumptions in the sharp truncation comparison follow
from Schwartz regularity and the single normalization value at zero. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem schwartzProfile_bounds (a : SchwartzMap ℝ ℂ) (ha : a 0= -1) :
    ∃ D : ℝ, 0≤D ∧ (∀ s, ‖a s+1‖≤D*|s|) ∧ (∀ s, |s| *‖a s‖≤D) := by
  let D := SchwartzMap.seminorm ℝ 0 1 a+SchwartzMap.seminorm ℝ 1 0 a
  have h0 : 0≤SchwartzMap.seminorm ℝ 0 1 a := apply_nonneg _ _
  have h1 : 0≤SchwartzMap.seminorm ℝ 1 0 a := apply_nonneg _ _
  have hd (x : ℝ) : ‖deriv a x‖≤SchwartzMap.seminorm ℝ 0 1 a := by
    simpa only [pow_zero,one_mul,iteratedDeriv_one] using a.le_seminorm' ℝ 0 1 x
  refine ⟨D,add_nonneg h0 h1,?_,?_⟩
  · intro s
    have h := convex_univ.norm_image_sub_le_of_norm_deriv_le
      (fun x (_ : x∈(Set.univ : Set ℝ)) => a.differentiableAt)
      (fun x (_ : x∈(Set.univ : Set ℝ)) => hd x) (Set.mem_univ (0:ℝ)) (Set.mem_univ s)
    rw [ha,sub_neg_eq_add,sub_zero,Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right h1) (abs_nonneg s))
  · intro s
    have h := a.norm_pow_mul_le_seminorm ℝ 1 s
    simp only [pow_one,Real.norm_eq_abs] at h
    exact h.trans (le_add_of_nonneg_left h0)

theorem schwartzFiniteTimeKernel_sharp_integral (k a : SchwartzMap ℝ ℂ)
    (ha : a 0= -1) (hprofile : ∀ s : ℝ, (s : ℂ)*k s=a s-a (s/2)) :
    ∃ B : ℝ, 0≤B ∧ ∀ (N : ℕ) (topLength : ℝ), 0<topLength →
      Integrable (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        finiteTimeKernel k N topLength t) ∧
      (∫ t, ‖sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        finiteTimeKernel k N topLength t‖)≤B := by
  obtain ⟨D,hD,hnear,hfar⟩ := schwartzProfile_bounds a ha
  refine ⟨8*Real.pi*D,by positivity,?_⟩
  intro N topLength htop
  exact finiteTimeKernel_sharp_integral k a a.continuous.measurable hprofile
    D hD hnear hfar N topLength htop

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HilbertTimeProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual annular inverse Fourier kernel telescopes to a normalized
Schwartz profile. This gives a uniform sharp truncation comparison. -/
noncomputable section
open MeasureTheory FourierTransform LineDeriv
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertTimeProfile_zero : hilbertTimeProfile 0= -1 := by
  change (1/2:ℂ)*(𝓕⁻ hilbertCutoffDerivative : SchwartzMap ℝ ℂ) 0= -1
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq]
  simp only [inner_zero_right,Real.fourierChar.map_zero_eq_one,one_smul]
  rw [hilbertCutoffDerivative_integral]
  norm_num

theorem schwartzDilation_fourierInv (f : SchwartzMap ℝ ℂ) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    (𝓕⁻ (schwartzDilation f r hr.ne') : SchwartzMap ℝ ℂ) t=
      (r⁻¹:ℂ)*(𝓕⁻ f : SchwartzMap ℝ ℂ) (t/r) := by
  simp only [SchwartzMap.fourierInv_coe,Real.fourierInv_eq_fourier_neg]
  rw [←SchwartzMap.fourier_coe,schwartzDilation_fourier]
  rw [abs_of_pos (inv_pos.mpr hr),Complex.real_smul,neg_div]
  simp only [Complex.ofReal_inv,SchwartzMap.fourier_coe]

theorem schwartz_fourierInv_deriv (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    (𝓕⁻ (SchwartzMap.derivCLM ℂ ℂ f) : SchwartzMap ℝ ℂ) t=
      -(2*Real.pi*Complex.I)*(t:ℂ)*(𝓕⁻ f : SchwartzMap ℝ ℂ) t := by
  have heq : SchwartzMap.derivCLM ℂ ℂ f=∂_{(1:ℝ)} f := by
    ext x
    rw [SchwartzMap.derivCLM_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv,
      fderiv_apply_one_eq_deriv]
  rw [heq,SchwartzMap.fourierInv_lineDerivOp_eq]
  simp only [smul_apply,Real.inner_apply,mul_one,smul_eq_mul]
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (show (fun x : ℝ => x).HasTemperateGrowth from by fun_prop)]
  simp only [Complex.real_smul]
  ring

theorem hilbertTimeKernel_profile (t : ℝ) :
    (t:ℂ)*hilbertTimeKernel t=hilbertTimeProfile t-hilbertTimeProfile (t/2) := by
  have hd : SchwartzMap.derivCLM ℂ ℂ hilbertAnnularSymbol=
      (-(Real.pi:ℂ)*Complex.I) • (hilbertCutoffDerivative-
        (2:ℂ) • schwartzDilation hilbertCutoffDerivative 2 (by norm_num)) := by
    ext x
    simp only [SchwartzMap.derivCLM_apply,smul_apply,sub_apply,smul_eq_mul,
      schwartzDilation_apply]
    exact hilbertAnnularSymbol_deriv x
  have h := schwartz_fourierInv_deriv hilbertAnnularSymbol t
  rw [hd] at h
  simp only [sub_eq_add_neg,fourierInv_add,fourierInv_neg,fourierInv_smul,
    smul_apply,add_apply,neg_apply,smul_eq_mul] at h
  rw [schwartzDilation_fourierInv hilbertCutoffDerivative 2 (by norm_num) t] at h
  change (t:ℂ)*(𝓕⁻ hilbertAnnularSymbol : SchwartzMap ℝ ℂ) t=
    (1/2:ℂ)*(𝓕⁻ hilbertCutoffDerivative : SchwartzMap ℝ ℂ) t-
      (1/2:ℂ)*(𝓕⁻ hilbertCutoffDerivative : SchwartzMap ℝ ℂ) (t/2)
  have hp : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  apply (mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (by norm_num : (-2:ℂ)≠0) hp) Complex.I_ne_zero))
  calc
    _ = -(2*Real.pi*Complex.I)*(t:ℂ)*(𝓕⁻ hilbertAnnularSymbol : SchwartzMap ℝ ℂ) t := by ring
    _ = _ := h.symm
    _ = _ := by push_cast; ring

theorem hilbertTimeKernel_sharp_integral :
    ∃ B : ℝ, 0≤B ∧ ∀ (N : ℕ) (topLength : ℝ), 0<topLength →
      Integrable (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        finiteTimeKernel hilbertTimeKernel N topLength t) ∧
      (∫ t, ‖sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        finiteTimeKernel hilbertTimeKernel N topLength t‖)≤B :=
  schwartzFiniteTimeKernel_sharp_integral hilbertTimeKernel hilbertTimeProfile
    hilbertTimeProfile_zero hilbertTimeKernel_profile

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TimeEndpointComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A factor-two change of the inner time endpoint costs a fixed L1
constant. Every positive inner endpoint has such a dyadic representative. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_close_lower (r s R t : ℝ) (hr : 0 < r)
    (hrs : r ≤ s) (hsr : s≤2*r) :
    ‖sharpTimeKernel r R t-sharpTimeKernel s R t‖≤3*timeErrorEnvelope r t := by
  have hq := timeErrorEnvelope_nonneg r t hr
  by_cases hs : s< |t|
  · have hr' : r< |t| := hrs.trans_lt hs
    simp only [sharpTimeKernel,hr',hs,true_and,sub_self,norm_zero]
    positivity
  · by_cases hr' : r< |t|
    · by_cases hR : |t|<R
      · have ht : 0< |t| := hr.trans hr'
        have ht2 : |t|≤2*r := (le_of_not_gt hs).trans hsr
        have hd : 0 < r^2+t^2 := by positivity
        have hpoly : r^2+t^2≤3*r*|t| := by
          nlinarith [sq_abs t,mul_nonneg (sub_nonneg.mpr hr'.le) (sub_nonneg.mpr ht2)]
        have hcond1 : r< |t| ∧ |t|<R := ⟨hr',hR⟩
        have hcond2 : ¬(s< |t| ∧ |t|<R) := fun h => hs h.1
        simp only [sharpTimeKernel,ite_eq_left hcond1,ite_eq_right hcond2,sub_zero,
          norm_inv,Complex.norm_real,Real.norm_eq_abs,timeErrorEnvelope]
        rw [←mul_div_assoc,inv_eq_one_div]
        apply (div_le_div_iff₀ ht hd).2
        nlinarith only [hpoly]
      · have hcond1 : ¬(r< |t| ∧ |t|<R) := fun h => hR h.2
        have hcond2 : ¬(s< |t| ∧ |t|<R) := fun h => hR h.2
        simp only [sharpTimeKernel,ite_eq_right hcond1,ite_eq_right hcond2,sub_self,norm_zero]
        positivity
    · have hcond1 : ¬(r< |t| ∧ |t|<R) := fun h => hr' h.1
      have hcond2 : ¬(s< |t| ∧ |t|<R) := fun h => hs h.1
      simp only [sharpTimeKernel,ite_eq_right hcond1,ite_eq_right hcond2,sub_self,norm_zero]
      positivity

theorem sharpTimeKernel_close_lower_integral (r s R : ℝ) (hr : 0 < r)
    (hrs : r ≤ s) (hsr : s≤2*r) :
    Integrable (fun t => sharpTimeKernel r R t-sharpTimeKernel s R t) ∧
      (∫ t, ‖sharpTimeKernel r R t-sharpTimeKernel s R t‖)≤3*Real.pi := by
  have hm := (sharpTimeKernel_measurable r R).sub (sharpTimeKernel_measurable s R)
  have hi := (timeErrorEnvelope_integrable r hr).const_mul 3
  have hb (t) := sharpTimeKernel_close_lower r s R t hr hrs hsr
  have he := hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨he,?_⟩
  calc
    _ ≤ ∫ t, 3*timeErrorEnvelope r t := integral_mono he.norm hi hb
    _ = 3*Real.pi := by rw [integral_const_mul,timeErrorEnvelope_integral r hr]

theorem exists_dyadic_time_endpoint (epsilon R : ℝ) (he : 0<epsilon) (heR : epsilon≤R) :
    ∃ N : ℕ, epsilon≤R/(2:ℝ)^N ∧ R/(2:ℝ)^N<2*epsilon := by
  have hR : 0<R := he.trans_le heR
  obtain ⟨N,hlo,hhi⟩ := exists_nat_pow_near ((le_div_iff₀ he).2 (by simpa using heR))
    (by norm_num : (1:ℝ)<2)
  refine ⟨N,?_,?_⟩
  · apply (le_div_iff₀ (pow_pos (by norm_num) N)).2
    simpa only [mul_comm] using (le_div_iff₀ he).1 hlo
  · apply (div_lt_iff₀ (pow_pos (by norm_num) N)).2
    have h := (div_lt_iff₀ he).1 hhi
    rw [pow_succ] at h
    nlinarith only [h]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HilbertArbitraryEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Hilbert decomposition applies to every positive inner
truncation, with a nearby dyadic endpoint and a uniform error. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertTimeKernel_arbitrary_endpoint :
    ∃ B : ℝ, 0≤B ∧ ∀ epsilon R : ℝ, 0<epsilon → epsilon≤R →
      ∃ N : ℕ, epsilon≤R/(2:ℝ)^N ∧ R/(2:ℝ)^N<2*epsilon ∧
        Integrable (fun t => sharpTimeKernel epsilon R t-
          finiteTimeKernel hilbertTimeKernel N (R/2) t) ∧
        (∫ t, ‖sharpTimeKernel epsilon R t-
          finiteTimeKernel hilbertTimeKernel N (R/2) t‖)≤B := by
  obtain ⟨B,hB,hkernel⟩ := hilbertTimeKernel_sharp_integral
  refine ⟨3*Real.pi+B,by positivity,?_⟩
  intro epsilon R he heR
  have hR : 0<R := he.trans_le heR
  obtain ⟨N,hlo,hhi⟩ := exists_dyadic_time_endpoint epsilon R he heR
  refine ⟨N,hlo,hhi,?_⟩
  have hc := sharpTimeKernel_close_lower_integral epsilon (R/(2:ℝ)^N) R he hlo hhi.le
  have hk := hkernel N (R/2) (by positivity)
  rw [show 2*(R/2)=R by ring] at hk
  let A := fun t => sharpTimeKernel epsilon R t-sharpTimeKernel (R/(2:ℝ)^N) R t
  let C := fun t => sharpTimeKernel (R/(2:ℝ)^N) R t-
    finiteTimeKernel hilbertTimeKernel N (R/2) t
  have hi : Integrable (fun t => sharpTimeKernel epsilon R t-
      finiteTimeKernel hilbertTimeKernel N (R/2) t) := by
    apply (hc.1.add hk.1).congr
    filter_upwards [] with t
    dsimp
    ring
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ t, ‖A t‖+‖C t‖ := by
      apply integral_mono hi.norm (hc.1.norm.add hk.1.norm)
      intro t
      have heq : sharpTimeKernel epsilon R t-finiteTimeKernel hilbertTimeKernel N (R/2) t=
          A t+C t := by dsimp [A,C]; ring
      change ‖sharpTimeKernel epsilon R t-finiteTimeKernel hilbertTimeKernel N (R/2) t‖≤
        ‖A t‖+‖C t‖
      rw [heq]
      exact norm_add_le _ _
    _ = (∫ t, ‖A t‖)+(∫ t, ‖C t‖) := integral_add hc.1.norm hk.1.norm
    _ ≤ 3*Real.pi+B := add_le_add hc.2 hk.2

theorem hilbertArbitraryEndpoint_pairing :
    ∃ B : ℝ, 0≤B ∧ ∀ epsilon R : ℝ, 0<epsilon → epsilon≤R →
      ∃ N : ℕ, epsilon≤R/(2:ℝ)^N ∧ R/(2:ℝ)^N<2*epsilon ∧
      ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u →
      ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      ∀ l r : ℝ, r-l≤1/4 →
        (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      ‖(∫ z, slopeKernelOperator (sharpTimeKernel epsilon R) u f z*star (g z) ∂planeMeasure)-
        (∫ z, slopeKernelOperator (finiteTimeKernel hilbertTimeKernel N (R/2))
          u f z*star (g z) ∂planeMeasure)‖≤
        B*min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
  obtain ⟨B,hB,hkernel⟩ := hilbertTimeKernel_arbitrary_endpoint
  refine ⟨B,hB,?_⟩
  intro epsilon R he heR
  have hR : 0<R := he.trans_le heR
  obtain ⟨N,hlo,hhi,herror,hbound⟩ := hkernel epsilon R he heR
  refine ⟨N,hlo,hhi,?_⟩
  intro u hu f g hf1 hg1 l r hwidth hfstrip hgstrip
  have hJ := finiteTimeKernel_integrable hilbertTimeKernel N (R/2) (by positivity)
  have hK : Integrable (sharpTimeKernel epsilon R) := by
    apply (herror.add hJ).congr
    filter_upwards [] with t
    simp only [Pi.add_apply,sub_add_cancel]
  have h := kernelDifference_pairing (sharpTimeKernel epsilon R)
    (finiteTimeKernel hilbertTimeKernel N (R/2)) (sharpTimeKernel_measurable _ _)
    (finiteTimeKernel_measurable _ _ _) hK hJ u hu f g hf1 hg1 l r hwidth hfstrip hgstrip
  exact h.trans ((mul_le_mul_of_nonneg_left hbound
    (le_min (by positivity) (integral_nonneg fun _ => norm_nonneg _))).trans_eq (mul_comm _ _))

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

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnnularPacketGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed numerical choices for the annular multiplier. The enlargement
and compact master radius depend only on its support and on the two
frequency-window widths. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

namespace AnnularPacketGeometry
variable {A B c C a M : ℝ} (p : AnnularPacketGeometry A B c C a M)

theorem outer_pos : 0<p.outer := by unfold outer; positivity [p.H_pos,p.hc,p.hM,p.hA]

theorem parameter_bound (w W center : ℝ) (hw : 0<w) (hW : 0<W)
    (hwW : p.H*w≤W)
    (hlo : c+B*(w/W)≤w*center) (hhi : w*center+B*(w/W)≤C) :
    ‖(p.H*w*center,p.H*w/W)‖≤p.R := by
  have hratio : 0≤w/W := (div_pos hw hW).le
  have hpad : 0≤B*(w/W) := mul_nonneg p.hB hratio
  have hcenter : 0≤w*center := by linarith [p.hc]
  have hcenterHi : w*center≤C := by linarith
  have hleft : |p.H*w*center|≤p.H*C := by
    rw [abs_of_nonneg (by nlinarith [p.H_pos])]
    nlinarith [p.H_pos]
  have hright : |p.H*w/W|≤p.H := by
    rw [abs_of_pos (div_pos (mul_pos p.H_pos hw) hW)]
    have hh : p.H*w/W≤1 := (div_le_one hW).mpr hwW
    exact hh.trans p.hH
  rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
  exact (max_le_max hleft hright).trans p.radius

end AnnularPacketGeometry

/-- The required geometry follows from a narrow horizontal window; all
large constants are chosen before the scale, carrier, or row families. -/
theorem exists_annular_packet_geometry (A B c C a M : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hnarrow : A≤a/4) (hsep : A/c<(3*a/(4*C)/2)/4) :
    Nonempty (AnnularPacketGeometry A B c C a M) := by
  let a0 := 3*a/(4*C)
  let b0 := (M+A)/c
  have ha0 : 0<a0 := by dsimp [a0]; positivity
  have hb0 : 0<b0 := by dsimp [b0]; positivity
  obtain ⟨H,hH⟩ := exists_gt (max 1 (max (2*a0) (6*max (2*b0) (A/c+a0/2))))
  have hH1 : 1≤H := ((le_max_left _ _).trans hH.le)
  have hHp : 0<H := zero_lt_one.trans_le hH1
  have hHa : 2*a0<H := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hH)
  have hHcover : 6*max (2*b0) (A/c+a0/2)<H :=
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hH)
  let R := 1+max (A+B+(M+A)/(H*c)) (max (H*C) H)
  have hR : 0<R := by
    dsimp only [R]
    have h := (le_max_right (A+B+(M+A)/(H*c)) (max (H*C) H)).trans' (le_max_right (H*C) H)
    linarith
  have hpi : (2*Real.pi*A)/(2*Real.pi*(H*c))=(A/c)/H := by
    field_simp [Real.pi_ne_zero,hHp.ne',hc.ne']
  have haH : 3*a/(4*(H*C))=a0/H := by dsimp [a0]; ring
  have hbH : (M+A)/(H*c)=b0/H := by dsimp [b0]; ring
  refine ⟨⟨H,R,hA,hB,hc,hC,ha,hM,hH1,hR,hnarrow,?_,?_,?_,?_,?_⟩⟩
  · dsimp only [R]
    linarith [le_max_left (A+B+(M+A)/(H*c)) (max (H*C) H)]
  · dsimp only [R]
    linarith [le_max_right (A+B+(M+A)/(H*c)) (max (H*C) H)]
  · rw [haH]
    have hh : a0/H≤1/2 := (div_le_iff₀ hHp).mpr (by linarith)
    linarith
  · rw [hpi,haH,show (a0/H/2)/4=(a0/2/4)/H by ring]
    exact div_lt_div_of_pos_right hsep hHp
  · rw [hpi,haH,hbH,show 2*(b0/H)=(2*b0)/H by ring,
      show (A/c)/H+(a0/H)/2=(A/c+a0/2)/H by ring,max_div_div_right hHp.le]
    have hh := (div_lt_one hHp).mpr hHcover
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_DiagonalGeometryChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete choice of the narrow frequency plateau and slope spacing
for every fixed positive annular support. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem exists_diagonal_geometry (B c C a M : ℝ) (hB : 0<B)
    (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M) :
    ∃ A delta : ℝ, ∃ _p : AnnularPacketGeometry A B c C a M,
      0<A ∧ 0<delta ∧ delta*C≤A/2 := by
  let A := min (a/8) (3*a*c/(128*C))
  have hA : 0<A := lt_min (by positivity) (by positivity)
  have hnarrow : A≤a/4 := (min_le_left _ _).trans (by linarith)
  have hAc : A/c≤3*a/(128*C) := by
    apply (div_le_iff₀ hc).mpr
    convert min_le_right (a/8) (3*a*c/(128*C)) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hsep : A/c<(3*a/(4*C)/2)/4 := by
    have hp : 0<3*a/(128*C) := by positivity
    have heq : (3*a/(4*C)/2)/4=4*(3*a/(128*C)) := by ring
    rw [heq]
    linarith
  obtain ⟨p⟩ := exists_annular_packet_geometry A B c C a M hA.le hB.le hc hC ha hM hnarrow hsep
  let delta := A/(4*C)
  have hd : 0<delta := by dsimp [delta]; positivity
  have hdelta : delta*C≤A/2 := by
    have heq : delta*C=A/4 := by dsimp [delta]; field_simp
    rw [heq]
    linarith
  exact ⟨A,delta,p,hA,hd,hdelta⟩

theorem center_frequency_bounds (B c C w W center : ℝ)
    (hB : 0≤B) (hc : 0 < c) (hw : 0<w) (hW : 0<W)
    (hlo : c+B*(w/W)≤w*center) (hhi : w*center+B*(w/W)≤C) :
    (2*Real.pi*c)/w≤|2*Real.pi*center| ∧ |2*Real.pi*center|≤(2*Real.pi*C)/w := by
  have hp : 0≤B*(w/W) := by positivity
  have hcenter : 0 < center := by nlinarith
  rw [abs_of_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hcenter)]
  constructor
  · apply (div_le_iff₀ hw).mpr
    nlinarith [Real.pi_pos]
  · apply (le_div_iff₀ hw).mpr
    nlinarith [Real.pi_pos]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NormalizedProfileBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the finite derivative order and Fourier-decay exponent before
any packet lattice. Their fixed profile cost fits the model's logarithmic
budget once the disparity parameter is large enough. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem requiredPacketOrder_basic (D : ℕ) :
    207 ≤ requiredPacketOrder D ∧ 6+2*(8*D+1) ≤ requiredPacketOrder D :=
  ⟨le_max_left _ _,le_max_right _ _⟩

theorem exists_normalized_profile_budget (F G : SchwartzMap (ℝ×ℝ) ℂ) (D : ℕ) :
    ∃ q : ℕ, 4≤q ∧ ∃ C L₀ : ℝ, 0<C ∧ 16≤L₀ ∧
      (∀ nu : SymbolSpace,
        planarProfileConstant (synthesisProfile F q nu) (2*requiredPacketOrder D) ≤ C ∧
        planarProfileConstant (analysisProfile G q nu) (2*requiredPacketOrder D) ≤ C) ∧
      ∀ L : ℝ, L₀≤L →
        ((2:ℝ)^requiredPacketOrder D*C)*3^(2*requiredPacketOrder D) ≤ L^(1:ℝ) := by
  obtain ⟨q₀,C,hC,hprofiles⟩ := uniform_normalized_profile_pair F G (2*requiredPacketOrder D)
  let budget : ℝ := (2^requiredPacketOrder D*C)*3^(2*requiredPacketOrder D)
  refine ⟨max 4 q₀,le_max_left _ _,C,max 16 budget,hC,le_max_left _ _,?_,?_⟩
  · exact hprofiles (max 4 q₀) (le_max_right _ _)
  · intro L hL
    rw [Real.rpow_one]
    exact (le_max_right 16 budget).trans hL

end LipschitzHilbert.PacketRepresentation

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

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PartitionedAnnularFormL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite representation including the manuscript slope partition
and the vertical bin window. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]

theorem normalizedSymbolSum_eq_partitioned_annular_l1
    (psi rho beta : SchwartzMap ℝ ℂ) (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ)
    (A B c C a M R H : ℝ) (hR : 0<R) (hH : 0<H)
    (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hA : 0≤A) (hsmall : A≤a/4)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hsize : A+B+(M+A)/(H*c)≤R)
    (hchiA : ∀ z, chiA z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (topLength width w : ℝ) (htop : 0<topLength) (hwidth : 0<width) (hw : 0<w)
    (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (hparam : ∀ k, ‖(H*w*center k,H*w/width)‖≤R)
    (hlo : ∀ k, c+B*(w/width)≤w*center k)
    (hhi : ∀ k, w*center k+B*(w/width)≤C)
    (u : ℝ×ℝ → ℝ) (f : κ → (ℝ×ℝ) → ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    normalizedSymbolSumL1 chiA chiB
      (annularCutoff (3*a/(4*(H*C))) ((M+A)/(H*c)) (by positivity) (by positivity))
      topLength width (H*w) htop hwidth labels theta center
      (fun _ k => partitionedSymbol psi (dilatedSlopeWindow rho H hH.ne') beta (H*c) (mul_pos hH hc) R hR (H*w*center k) (H*w/width)) u f g =
      partitionedAnnularSumL1 psi rho beta chiA chiB topLength width w htop hwidth labels theta center u f g := by
  classical
  unfold normalizedSymbolSumL1 partitionedAnnularSumL1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with omega
  by_cases hz : latticeFrequencyWindow chiA topLength width htop hwidth labels theta center i k omega=0
  · simp only [hz,zero_mul,mul_zero,smul_zero]
  have hwindow : latticeFrequencyWindow chiA topLength width htop hwidth labels theta center i k omega=
      chiA (symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2),
        symbolY width omega.2 (center k)) := by
    exact scaledWindow_inverse_profile_apply chiA _ width _ _
      (latticeLength_pos topLength htop labels i) hwidth omega.1 omega.2
  obtain ⟨hX,hY⟩ := hchiA _ (by simpa only [hwindow] using hz)
  obtain ⟨hVlo,hVhi⟩ := vertical_annulus_from_window w width (center k) omega.2 B c C
    hw hwidth (hlo k) (hhi k) hY
  have heq := rescaled_partitioned_symbol_eq psi rho beta A B c C a M R H hR hH hc hC ha hM hA hsmall
    hpsi hsize (latticeLength topLength labels i) w width (theta i.1 i.2) (center k) (u z)
    omega.1 omega.2 (latticeLength_pos topLength htop labels i) hw hwidth (hparam k) hX hY hVlo hVhi
  simp only [Circle.smul_def,smul_eq_mul]
  calc
    _ = (Real.fourierChar (z.1*omega.1+z.2*omega.2):ℂ)*
        (((annularCutoff (3*a/(4*(H*C))) ((M+A)/(H*c)) (by positivity) (by positivity)
          (symbolU (latticeLength topLength labels i) (H*w) (u z) (theta i.1 i.2)):ℂ)*
          partitionedSymbol psi (dilatedSlopeWindow rho H hH.ne') beta (H*c) (mul_pos hH hc) R hR (H*w*center k) (H*w/width)
            (symbolPoint (symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2))
              (symbolY width omega.2 (center k))
              (symbolU (latticeLength topLength labels i) (H*w) (u z) (theta i.1 i.2))))*
          (latticeFrequencyWindow chiA topLength width htop hwidth labels theta center i k omega*
            latticeFrequencyWindow chiB topLength width htop hwidth labels theta center i k omega*
            planarFourier (f k) omega)) := by ring
    _ = _ := by rw [heq]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PartitionedAnnularBasicL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite partitioned annular multiplier has a uniform basic bound.
The fixed symbol and profile costs are constructed, not assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_partitioned_annular_basic_l1 (hVariation : LepingleInput)
    (psi rho beta : SchwartzMap ℝ ℂ) (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ)
    (A B c C a M : ℝ) (p : AnnularPacketGeometry A B c C a M) (multiplicity : ℕ)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hchiA : ∀ z, chiA z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (hchiB : ∀ z, chiB z≠0 → |z.1|≤A ∧ |z.2|≤B) :
    ∃ K : ℝ, 0<K ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) [Fintype κ]
      (topLength width w F : ℝ) (htop : 0<topLength) (hwidth : 0<width),
      0<w → p.H*w≤width → 0≤F →
    ∀ (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ),
      (∀ k, |2*Real.pi*center k|≤F/(p.H*w)) →
      (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (theta j)
        ((p.H*w)/(topLength/(2:ℝ)^j.val)) multiplicity) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
    ∀ (f : κ → (ℝ×ℝ) → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ k, Integrable (f k) planeMeasure) → (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
      (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
      ‖partitionedAnnularSumL1 psi rho beta chiA chiB topLength width w htop hwidth
        labels theta center u f g‖≤
        K*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E) := by
  obtain ⟨q,hq,Cprofile,_Lp,hCp,_hLp,hprofiles,_hbudget⟩ :=
    exists_normalized_profile_budget (planarInverseSchwartz chiA) (planarInverseSchwartz chiB) 0
  obtain ⟨Csymbol,hCs,hS⟩ := partitionedSymbol_uniform psi (dilatedSlopeWindow rho p.H p.H_pos.ne') beta
    (p.H*c) (mul_pos p.H_pos p.hc) p.R p.hR q
  obtain ⟨K,hK,hbasic⟩ := exists_normalized_symbol_basic_l1 hVariation chiA chiB q hq
    A B (2*Real.pi*(p.H*c)) (2*Real.pi*(p.H*C)) p.inner p.outer Cprofile Csymbol
    multiplicity (requiredPacketOrder 0) p.hA p.hB (by positivity [p.H_pos,p.hc])
    (by positivity [p.H_pos,p.hC]) p.inner_pos p.outer_pos p.quarter
    hCp hCs (requiredPacketOrder_basic 0).1 p.separation p.coverage p.numerics
    hchiA hchiB hprofiles
  refine ⟨K,hK,?_⟩
  intro N κ Label _ topLength width w F htop hwidth hw hW hF labels theta center
    hfrequency hlo hhi hlocal u hu f fData g hfint hf hfm hgm hfb hgb E Fset
    hE hFset hEfin hFfin hgs hfs
  have hscaledLo (k : κ) : 2*Real.pi*(p.H*c)+(2*Real.pi*B)*((p.H*w)/width)≤
      (p.H*w)*(2*Real.pi*center k) := by
    first | (convert mul_le_mul_of_nonneg_left (hlo k) (show 0≤2*Real.pi*p.H by positivity [p.H_pos]) using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((mul_le_mul_of_nonneg_left (hlo k) (show 0≤2*Real.pi*p.H by positivity [p.H_pos])).trans (le_of_eq (by ring)))
  have hscaledHi (k : κ) : (p.H*w)*(2*Real.pi*center k)+(2*Real.pi*B)*((p.H*w)/width)≤
      2*Real.pi*(p.H*C) := by
    first | (convert mul_le_mul_of_nonneg_left (hhi k) (show 0≤2*Real.pi*p.H by positivity [p.H_pos]) using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((mul_le_mul_of_nonneg_left (hhi k) (show 0≤2*Real.pi*p.H by positivity [p.H_pos])).trans (le_of_eq (by ring)))
  rw [←normalizedSymbolSum_eq_partitioned_annular_l1 psi rho beta chiA chiB A B c C a M p.R p.H p.hR p.H_pos
    p.hc p.hC p.ha p.hM p.hA p.narrow hpsi p.size hchiA topLength width w htop hwidth hw
    labels theta center (fun k => p.parameter_bound w width (center k) hw hwidth hW (hlo k) (hhi k))
    hlo hhi u f g]
  exact hbasic N κ Label topLength width (p.H*w) F htop hwidth (mul_pos p.H_pos hw) hW hF
    labels theta center hfrequency hscaledLo hscaledHi hlocal
    (fun _ k => partitionedSymbol psi (dilatedSlopeWindow rho p.H p.H_pos.ne') beta
      (p.H*c) (mul_pos p.H_pos p.hc) p.R p.hR (p.H*w*center k) (p.H*w/width))
    (fun _ k => hS _ _) u hu f fData g hfint hf hfm hgm hfb hgb E Fset
    hE hFset hEfin hFfin hgs hfs

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_RectangularFrequencyCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed rectangular plateau supplies both convolution factors in the
finite band representation. -/
noncomputable section
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem rectangularFrequencyCutoff_apply (A B : ℝ) (hA : 0<A) (hB : 0<B) (z : ℝ×ℝ) :
    rectangularFrequencyCutoff A B hA hB z=(unitPlaneBump (z.1/(A/2),z.2/(B/2)):ℂ) := by
  change (unitPlaneBump (z.1/(A/2),(z.2-0*z.1)/(B/2)):ℂ)=_
  simp only [zero_mul,sub_zero]

theorem rectangularFrequencyCutoff_one (A B : ℝ) (hA : 0<A) (hB : 0<B) (z : ℝ×ℝ)
    (hx : |z.1|≤A/2) (hy : |z.2|≤B/2) : rectangularFrequencyCutoff A B hA hB z=1 := by
  rw [rectangularFrequencyCutoff_apply]
  have hn : ‖(z.1/(A/2),z.2/(B/2))‖≤1 := by
    change max |z.1/(A/2)| |z.2/(B/2)|≤1
    simp only [abs_div,abs_of_pos hA,abs_of_pos hB,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact max_le ((div_le_one (by positivity)).mpr hx) ((div_le_one (by positivity)).mpr hy)
  have ho : unitPlaneBump (z.1/(A/2),z.2/(B/2))=1 :=
    unitPlaneBump.one_of_mem_closedBall (by
      change dist (z.1/(A/2),z.2/(B/2)) 0≤1
      rw [dist_zero_right]
      exact hn)
  rw [ho]
  norm_num

theorem rectangularFrequencyCutoff_support (A B : ℝ) (hA : 0<A) (hB : 0<B) (z : ℝ×ℝ)
    (hz : rectangularFrequencyCutoff A B hA hB z≠0) : |z.1|≤A ∧ |z.2|≤B := by
  have hn : ‖(z.1/(A/2),z.2/(B/2))‖<2 := by
    by_contra h
    have hzero : unitPlaneBump (z.1/(A/2),z.2/(B/2))=0 :=
      unitPlaneBump.zero_of_le_dist (by
        change 2≤dist (z.1/(A/2),z.2/(B/2)) 0
        rw [dist_zero_right]
        exact le_of_not_gt h)
    apply hz
    rw [rectangularFrequencyCutoff_apply,hzero]
    norm_num
  change max |z.1/(A/2)| |z.2/(B/2)|<2 at hn
  simp only [abs_div,abs_of_pos hA,abs_of_pos hB,abs_of_pos (by norm_num : (0:ℝ)<2),max_lt_iff] at hn
  constructor
  · have hh := (div_lt_iff₀ (by positivity : 0<A/2)).mp hn.1
    linarith
  · have hh := (div_lt_iff₀ (by positivity : 0<B/2)).mp hn.2
    linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_IntegerSlopeMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed angular lattice has local multiplicity independently of
its finite truncation. These bounds supply the model's label hypothesis. -/
noncomputable section
namespace LipschitzHilbert.SourceSlopeLabels

 theorem integer_slope_multiplicity_one (labels : Finset ℤ) (offset spacing : ℝ)
    (hspacing : 0 < spacing) :
    LocalMultiplicity labels (fun n : ℤ => offset+spacing*(n:ℝ)) spacing 1 := by
  classical
  intro a
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  have hupper : spacing*((i:ℝ)-(j:ℝ)) < spacing := by linarith
  have hlower : spacing*((j:ℝ)-(i:ℝ)) < spacing := by linarith
  have hu : (i:ℝ)-(j:ℝ)<1 := (mul_lt_mul_iff_right₀ hspacing).mp (by nlinarith only [hupper])
  have hl : (j:ℝ)-(i:ℝ)<1 := (mul_lt_mul_iff_right₀ hspacing).mp (by nlinarith only [hlower])
  have habs : |(i:ℝ)-(j:ℝ)|<1 := abs_lt.mpr ⟨by linarith,hu⟩
  have hInt : |i-j|<(1:ℤ) := by exact_mod_cast habs
  have habsInt := abs_lt.mp hInt
  omega

 theorem integer_slope_multiplicity (labels : Finset ℤ) (offset spacing precision : ℝ)
    (hspacing : 0 < spacing) (_hprecision : 0≤precision) (K : ℕ)
    (hK : precision≤2*K*spacing) :
    LocalMultiplicity labels (fun n : ℤ => offset+spacing*(n:ℝ)) precision (2*K+1) := by
  classical
  intro a
  have hlocal := integer_slope_multiplicity_one labels offset spacing hspacing
  apply (Finset.card_le_card (show labels.filter (fun n : ℤ =>
      a≤offset+spacing*(n:ℝ) ∧ offset+spacing*(n:ℝ)<a+precision) ⊆
      window labels (fun n : ℤ => offset+spacing*(n:ℝ)) (a+precision/2) spacing K from ?_)).trans
    ((window_card_le labels (fun n : ℤ => offset+spacing*(n:ℝ)) hspacing hlocal
      (le_refl (K:ℝ))).trans_eq (by omega))
  intro n hn
  obtain ⟨hn,hlo,hhi⟩ := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨hn,abs_le.mpr ⟨?_,?_⟩⟩ <;> nlinarith

end LipschitzHilbert.SourceSlopeLabels

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SlopePartitionGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite smooth partition uses the same arithmetic labels as
the packet model; their local multiplicity is uniform in the truncation. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceSlopeLabels

theorem injective_integer_multiplicity {ι : Type*} [Fintype ι]
    (index : ι → ℤ) (hinj : Function.Injective index)
    (offset spacing precision : ℝ) (hs : 0 < spacing) (hp : 0≤precision)
    (K : ℕ) (hK : precision≤2*K*spacing) :
    LocalMultiplicity Finset.univ (fun i => offset+spacing*(index i:ℝ)) precision (2*K+1) := by
  classical
  have h := integer_slope_multiplicity (Finset.univ.image index) offset spacing precision hs hp K hK
  intro a
  apply (Finset.card_le_card_of_injOn index ?_ (fun _ _ _ _ heq => hinj heq)).trans (h a)
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,(Finset.mem_filter.mp hi).2⟩

end LipschitzHilbert.SourceSlopeLabels
namespace LipschitzHilbert.PacketRepresentation

theorem scaledSlopePartition_apply (delta : ℝ) (hd : 0<delta) (x : ℝ) :
    scaledSlopePartition delta hd x=slopePartition (x/delta) := by
  rw [scaledSlopePartition,dilatedSlopeWindow_apply]
  congr 1
  ring

theorem scaledSlopePartition_support (delta : ℝ) (hd : 0<delta) (x : ℝ)
    (hx : scaledSlopePartition delta hd x≠0) : |x|≤delta := by
  rw [scaledSlopePartition_apply] at hx
  have h := slopePartition_support _ hx
  rw [abs_div,abs_of_pos hd] at h
  exact (div_le_one hd).mp h

theorem finiteSlopePartition_sum (K : ℕ) (delta d s : ℝ) (hdelta : 0<delta) (hd : 0<d)
    (hcover : |s/(delta*d)|≤K) :
    ∑ n∈finiteSlopeLabels K,
      scaledSlopePartition delta hdelta ((s-finiteSlopeCenter K delta d n)/d)=1 := by
  have heq (n : ℕ) : scaledSlopePartition delta hdelta ((s-finiteSlopeCenter K delta d n)/d)=
      slopePartition (s/(delta*d)+K-(n:ℝ)) := by
    rw [scaledSlopePartition_apply]
    congr 1
    unfold finiteSlopeCenter
    field_simp
    ring
  simp_rw [heq]
  exact slopePartition_sum_one K (s/(delta*d)) hcover

theorem exists_finiteSlopeCenter_multiplicity (delta H : ℝ) (hdelta : 0<delta) (hH : 0≤H) :
    ∃ M : ℕ, ∀ (K : ℕ) (d : ℝ), 0<d →
      SourceSlopeLabels.LocalMultiplicity (Finset.univ : Finset (finiteSlopeLabels K))
        (fun n => finiteSlopeCenter K delta d n.val) (H*d) M := by
  obtain ⟨J,hJ⟩ := exists_nat_gt (H/(2*delta))
  refine ⟨2*J+1,?_⟩
  intro K d hd
  have hJ' := (div_lt_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hdelta)).mp hJ
  have hh : H*d≤2*J*(delta*d) := by nlinarith
  have hi : Function.Injective (fun n : finiteSlopeLabels K => (n.val:ℤ)) := by
    intro x y h
    change (x.val:ℤ)=(y.val:ℤ) at h
    exact Subtype.ext (Int.ofNat.inj h)
  have h := SourceSlopeLabels.injective_integer_multiplicity
    (fun n : finiteSlopeLabels K => (n.val:ℤ)) hi (-delta*d*K) (delta*d) (H*d)
    (mul_pos hdelta hd) (mul_nonneg hH hd.le) J hh
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  simp only [finiteSlopeCenter,Int.cast_natCast]
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PartitionedBandFormL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove the two auxiliary frequency plateaus from the actual
partitioned multiplier. They equal one on its contributing frequencies. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]

theorem partitionedAnnularSum_eq_finitePartitionedBand_l1
    (psi beta : SchwartzMap ℝ ℂ) (A B c C delta : ℝ)
    (hA : 0<A) (hB : 0<B) (hc : 0 < c) (hdelta : 0<delta) (hnarrow : delta*C≤A/2)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2)
    (topLength width w : ℝ) (htop : 0<topLength) (hwidth : 0<width) (hw : 0<w)
    (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (hlo : ∀ k, c+B*(w/width)≤w*center k)
    (hhi : ∀ k, w*center k+B*(w/width)≤C)
    (u : ℝ×ℝ → ℝ) (f : κ → (ℝ×ℝ) → ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    partitionedAnnularSumL1 psi (scaledSlopePartition delta hdelta) beta
      (rectangularFrequencyCutoff A B hA hB) (rectangularFrequencyCutoff A B hA hB)
      topLength width w htop hwidth labels theta center u f g=
      finitePartitionedBandL1 psi (scaledSlopePartition delta hdelta) beta topLength width w
        labels theta center u f g := by
  classical
  unfold partitionedAnnularSumL1 finitePartitionedBandL1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  apply integral_congr_ae
  filter_upwards [] with omega
  by_cases hb : beta (symbolY width omega.2 (center k))=0
  · simp only [hb,mul_zero,zero_mul,smul_zero]
  by_cases hr : scaledSlopePartition delta hdelta
      (-symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2)/(w*omega.2))=0
  · simp only [hr,mul_zero,zero_mul,smul_zero]
  have hY := hbeta _ hb
  have hY' : |symbolY width omega.2 (center k)|≤B := hY.trans (by linarith)
  obtain ⟨hVlo,hVhi⟩ := vertical_annulus_from_window w width (center k) omega.2 B c C
    hw hwidth (hlo k) (hhi k) hY'
  have hVp : 0<w*omega.2 := hc.trans_le hVlo
  have hX := scaledSlopePartition_support delta hdelta _ hr
  rw [abs_div,abs_neg,abs_of_pos hVp] at hX
  have hX' : |symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2)|≤A/2 :=
    ((div_le_iff₀ hVp).mp hX).trans ((mul_le_mul_of_nonneg_left hVhi hdelta.le).trans hnarrow)
  have hwindow : latticeFrequencyWindow (rectangularFrequencyCutoff A B hA hB)
      topLength width htop hwidth labels theta center i k omega=1 := by
    rw [show latticeFrequencyWindow (rectangularFrequencyCutoff A B hA hB)
      topLength width htop hwidth labels theta center i k omega=
      rectangularFrequencyCutoff A B hA hB
        (symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2),
          symbolY width omega.2 (center k)) from
      scaledWindow_inverse_profile_apply _ _ width _ _
        (latticeLength_pos topLength htop labels i) hwidth omega.1 omega.2]
    exact rectangularFrequencyCutoff_one A B hA hB _ hX' hY
  simp only [hwindow,one_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalWindowRescaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enlarge the vertical reference width together with the auxiliary
angular precision. This leaves the physical multiplier and W/w unchanged. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem verticallyRescaledWindow_apply (beta : SchwartzMap ℝ ℂ) (H : ℝ) (hH : 0<H) (y : ℝ) :
    verticallyRescaledWindow beta H hH y=beta (y/H) := by
  rw [verticallyRescaledWindow,dilatedSlopeWindow_apply]
  congr 1
  ring

theorem verticallyRescaledWindow_symbolY (beta : SchwartzMap ℝ ℂ)
    (H W eta center : ℝ) (hH : 0<H) :
    verticallyRescaledWindow beta H hH (symbolY (H*W) eta center)=beta (symbolY W eta center) := by
  rw [verticallyRescaledWindow_apply]
  congr 1
  unfold symbolY
  field_simp

theorem verticallyRescaledWindow_support (beta : SchwartzMap ℝ ℂ)
    (B H : ℝ) (hH : 0<H) (hbeta : ∀ y, beta y≠0 → |y|≤B/2)
    (y : ℝ) (hy : verticallyRescaledWindow beta H hH y≠0) : |y|≤(H*B)/2 := by
  rw [verticallyRescaledWindow_apply] at hy
  have h := hbeta (y/H) hy
  rw [abs_div,abs_of_pos hH] at h
  have hh := (div_le_iff₀ hH).mp h
  nlinarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalWindowRescalingL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem finitePartitionedBand_vertical_rescaling_l1 {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]
    (psi rho beta : SchwartzMap ℝ ℂ) (H : ℝ) (hH : 0<H)
    (topLength width w : ℝ) (labels : ∀ j, Finset (Label j))
    (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (u : ℝ×ℝ → ℝ) (f : κ → (ℝ×ℝ) → ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    finitePartitionedBandL1 psi rho (verticallyRescaledWindow beta H hH) topLength (H*width) w
      labels theta center u f g=finitePartitionedBandL1 psi rho beta topLength width w
        labels theta center u f g := by
  unfold finitePartitionedBandL1
  simp_rw [verticallyRescaledWindow_symbolY]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BoundedFrequencyMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded measurable frequency symbol can be paired with an L1 test
function. This justifies finite recombination before the uniform estimates. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem variableFrequencyMultiplier_measurable (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ)
    (hm : Measurable m) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Measurable (variableFrequencyMultiplier m f) := by
  have hp : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) =>
      (Real.fourierChar (p.1.1*p.2.1+p.1.2*p.2.2):ℂ)) := by fun_prop
  have hF : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => planarFourier f p.2) := by
    have heq : (planarFourierSchwartz f : ℝ×ℝ → ℂ)=planarFourier f :=
      funext (planarFourierSchwartz_apply f)
    exact (heq ▸ (planarFourierSchwartz f).continuous.measurable).comp measurable_snd
  exact ((hp.mul (hm.mul hF)).stronglyMeasurable.integral_prod_right').measurable

theorem variableFrequencyMultiplier_bound (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ)
    (C : ℝ) (hbound : ∀ z omega, ‖m (z,omega)‖≤C)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    ‖variableFrequencyMultiplier m f z‖≤C*∫ omega, ‖planarFourier f omega‖ ∂planeMeasure := by
  have h := norm_integral_le_of_norm_le ((planarFourier_integrable f).norm.const_mul C)
    (Filter.Eventually.of_forall (fun omega => show
      ‖Real.fourierChar (z.1*omega.1+z.2*omega.2) • (m (z,omega)*planarFourier f omega)‖≤
      C*‖planarFourier f omega‖ from by
        rw [Circle.norm_smul,norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound z omega) (norm_nonneg _)))
  simpa only [variableFrequencyMultiplier,planeMeasure,integral_const_mul] using h

theorem variableFrequencyMultiplier_pairing_integrable (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ)
    (hm : Measurable m) (C : ℝ) (hbound : ∀ z omega, ‖m (z,omega)‖≤C)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (g : ℝ×ℝ → ℂ) (hg : Integrable g planeMeasure) :
    Integrable (fun z => variableFrequencyMultiplier m f z*star (g z)) planeMeasure := by
  have hmeas := (variableFrequencyMultiplier_measurable m hm f).aestronglyMeasurable (μ:=planeMeasure)
  apply (hg.norm.const_mul (C*∫ omega, ‖planarFourier f omega‖ ∂planeMeasure)).mono'
    (hmeas.mul hg.aestronglyMeasurable.star)
  filter_upwards [] with z
  change ‖variableFrequencyMultiplier m f z*star (g z)‖≤_
  rw [norm_mul,norm_star]
  exact mul_le_mul_of_nonneg_right (variableFrequencyMultiplier_bound m C hbound f z) (norm_nonneg _)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PartitionedFrequencySymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete slope-partitioned frequency symbol is uniformly bounded
and measurable, including at the zero of its vertical denominator. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem partitionedFrequencySymbol_measurable (psi rho beta : SchwartzMap ℝ ℂ)
    (l W w theta center : ℝ) (u : ℝ×ℝ → ℝ) (hu : Measurable u) :
    Measurable (partitionedFrequencySymbol psi rho beta l W w theta center u) := by
  have hu' : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => u p.1) := hu.comp measurable_fst
  unfold partitionedFrequencySymbol symbolX symbolY
  apply Measurable.mul
  · apply Measurable.mul
    · apply psi.continuous.measurable.comp
      fun_prop
    · apply rho.continuous.measurable.comp
      fun_prop
  · apply beta.continuous.measurable.comp
    fun_prop

theorem partitionedFrequencySymbol_bound (psi rho beta : SchwartzMap ℝ ℂ)
    (l W w theta center : ℝ) (u : ℝ×ℝ → ℝ) (z omega : ℝ×ℝ) :
    ‖partitionedFrequencySymbol psi rho beta l W w theta center u (z,omega)‖≤
      SchwartzMap.seminorm ℝ 0 0 psi*SchwartzMap.seminorm ℝ 0 0 rho*SchwartzMap.seminorm ℝ 0 0 beta := by
  unfold partitionedFrequencySymbol
  rw [norm_mul,norm_mul]
  exact mul_le_mul
    (mul_le_mul (SchwartzMap.norm_le_seminorm ℝ psi _) (SchwartzMap.norm_le_seminorm ℝ rho _)
      (norm_nonneg _) (apply_nonneg _ _))
    (SchwartzMap.norm_le_seminorm ℝ beta _) (norm_nonneg _) (by positivity)

theorem sum_partitionedFrequencySymbol {ι : Type*} [Fintype ι]
    (psi rho beta : SchwartzMap ℝ ℂ) (l W w center : ℝ) (theta : ι → ℝ)
    (u : ℝ×ℝ → ℝ)
    (hpartition : ∀ z omega : ℝ×ℝ,
      psi (l*(omega.1+u z*omega.2))≠0 → beta (symbolY W omega.2 center)≠0 →
      ∑ i, rho (-symbolX l omega.1 omega.2 (theta i)/(w*omega.2))=1) :
    (fun p => ∑ i, partitionedFrequencySymbol psi rho beta l W w (theta i) center u p)=
      annularBandSymbol psi beta l W center u := by
  classical
  funext p
  rcases p with ⟨z,omega⟩
  unfold partitionedFrequencySymbol annularBandSymbol
  by_cases hp : psi (l*(omega.1+u z*omega.2))=0
  · simp only [hp,zero_mul,Finset.sum_const_zero]
  by_cases hb : beta (symbolY W omega.2 center)=0
  · simp only [hb,mul_zero,Finset.sum_const_zero]
  rw [←Finset.sum_mul,←Finset.mul_sum,hpartition z omega hp hb,mul_one]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularSlopePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On an annular multiplier, bounded output directions imply a finite
range of frequency slopes. The constructed arithmetic partition covers
that entire range, with no remaining partition-of-unity premise. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem annular_normalized_slope_bound (l w delta c M U u xi eta : ℝ)
    (hl : 0<l) (hw : 0<w) (hd : 0<delta) (hc : 0 < c) (hM : 0≤M)
    (hu : |u|≤U) (hfreq : |l*(xi+u*eta)|≤M) (hvertical : c≤w*eta) :
    |(-xi/eta)/(delta*(w/l))|≤U/(delta*(w/l))+M/(delta*c) := by
  have hdw : 0<delta*(w/l) := mul_pos hd (div_pos hw hl)
  have hV : 0<w*eta := hc.trans_le hvertical
  have heta : eta≠0 := by intro hz; rw [hz,mul_zero] at hV; exact (lt_irrefl 0 hV)
  have heq : (-xi/eta)/(delta*(w/l))=
      u/(delta*(w/l))-(l*(xi+u*eta))/(delta*(w*eta)) := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |u/(delta*(w/l))|+|(l*(xi+u*eta))/(delta*(w*eta))| := abs_sub _ _
    _ = |u|/(delta*(w/l))+|l*(xi+u*eta)|/(delta*(w*eta)) := by
      rw [abs_div,abs_div,abs_of_pos hdw,abs_of_pos (mul_pos hd hV)]
    _ ≤ U/(delta*(w/l))+M/(delta*c) := add_le_add
      (div_le_div_of_nonneg_right hu hdw.le)
      ((div_le_div_of_nonneg_right hfreq (mul_pos hd hV).le).trans
        (div_le_div_of_nonneg_left hM (mul_pos hd hc)
          (mul_le_mul_of_nonneg_left hvertical hd.le)))

theorem finiteSlopePartition_annular (psi beta : SchwartzMap ℝ ℂ)
    (K : ℕ) (l W w delta c M U center : ℝ)
    (hl : 0<l) (hw : 0<w) (hd : 0<delta) (hc : 0 < c) (hM : 0≤M)
    (hpsi : ∀ s : ℝ, psi s≠0 → |s|≤M)
    (hbeta : ∀ eta, beta (symbolY W eta center)≠0 → c≤w*eta)
    (hK : U/(delta*(w/l))+M/(delta*c)≤K)
    (u : ℝ×ℝ → ℝ) (hu : ∀ z, |u z|≤U)
    (z omega : ℝ×ℝ) (hp : psi (l*(omega.1+u z*omega.2))≠0)
    (hb : beta (symbolY W omega.2 center)≠0) :
    ∑ n : finiteSlopeLabels K, scaledSlopePartition delta hd
      (-symbolX l omega.1 omega.2 (finiteSlopeCenter K delta (w/l) n.val)/(w*omega.2))=1 := by
  have hV := hc.trans_le (hbeta omega.2 hb)
  have heta : omega.2≠0 := by intro hz; rw [hz,mul_zero] at hV; exact (lt_irrefl 0 hV)
  have hcover : |(-omega.1/omega.2)/(delta*(w/l))|≤K :=
    (annular_normalized_slope_bound l w delta c M U (u z) omega.1 omega.2
      hl hw hd hc hM (hu z) (hpsi _ hp) (hbeta _ hb)).trans hK
  have hsum := finiteSlopePartition_sum K delta (w/l) (-omega.1/omega.2) hd (div_pos hw hl) hcover
  rw [←Finset.sum_attach] at hsum
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  unfold symbolX
  field_simp
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_L1FrequencyMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrable frequency envelopes justify multipliers and finite
recombination for L1 inputs, including discontinuous amplitude slices. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem variableFrequencyMultiplier_measurable_l1
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : Measurable m)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) :
    Measurable (variableFrequencyMultiplierL1 m f) := by
  have hp : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) =>
      (Real.fourierChar (p.1.1*p.2.1+p.1.2*p.2.2):ℂ)) := by fun_prop
  have hF : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => planarFourier f p.2) :=
    (planarFourier_l1_continuous f hf).measurable.comp measurable_snd
  exact ((hp.mul (hm.mul hF)).stronglyMeasurable.integral_prod_right').measurable

theorem variableFrequencyMultiplier_integrand_integrable_l1
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : Measurable m)
    (q : ℝ×ℝ → ℝ) (hq : Integrable q planeMeasure)
    (hbound : ∀ z omega, ‖m (z,omega)‖≤q omega)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) (z : ℝ×ℝ) :
    Integrable (fun omega => Real.fourierChar (z.1*omega.1+z.2*omega.2) •
      (m (z,omega)*planarFourier f omega)) planeMeasure := by
  have hp : Measurable (fun omega : ℝ×ℝ =>
      (Real.fourierChar (z.1*omega.1+z.2*omega.2):ℂ)) := by fun_prop
  have hm' : Measurable (fun omega => m (z,omega)) :=
    hm.comp (measurable_const.prodMk measurable_id)
  apply (hq.mul_const (∫ x, ‖f x‖ ∂planeMeasure)).mono'
    (hp.mul (hm'.mul (planarFourier_l1_continuous f hf).measurable)).aestronglyMeasurable
  filter_upwards [] with omega
  change ‖(Real.fourierChar (z.1*omega.1+z.2*omega.2):ℂ)*
    (m (z,omega)*planarFourier f omega)‖≤_
  rw [norm_mul,Circle.norm_coe,one_mul,norm_mul]
  exact mul_le_mul (hbound z omega) (planarFourier_l1_bound f omega)
    (norm_nonneg _) ((norm_nonneg _).trans (hbound z omega))

theorem variableFrequencyMultiplier_bound_l1
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ)
    (q : ℝ×ℝ → ℝ) (hq : Integrable q planeMeasure)
    (hbound : ∀ z omega, ‖m (z,omega)‖≤q omega)
    (f : ℝ×ℝ → ℂ) (z : ℝ×ℝ) :
    ‖variableFrequencyMultiplierL1 m f z‖≤
      (∫ omega, q omega ∂planeMeasure)*(∫ x, ‖f x‖ ∂planeMeasure) := by
  have h := norm_integral_le_of_norm_le (hq.mul_const (∫ x, ‖f x‖ ∂planeMeasure))
    (Filter.Eventually.of_forall (fun omega => show
      ‖Real.fourierChar (z.1*omega.1+z.2*omega.2) • (m (z,omega)*planarFourier f omega)‖≤
        q omega*(∫ x, ‖f x‖ ∂planeMeasure) from by
      rw [Circle.norm_smul,norm_mul]
      exact mul_le_mul (hbound z omega) (planarFourier_l1_bound f omega)
        (norm_nonneg _) ((norm_nonneg _).trans (hbound z omega))))
  simpa only [variableFrequencyMultiplierL1,planeMeasure,integral_mul_const] using h

theorem variableFrequencyMultiplier_pairing_integrable_l1
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : Measurable m)
    (q : ℝ×ℝ → ℝ) (hq : Integrable q planeMeasure)
    (hbound : ∀ z omega, ‖m (z,omega)‖≤q omega)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure)
    (g : ℝ×ℝ → ℂ) (hg : Integrable g planeMeasure) :
    Integrable (fun z => variableFrequencyMultiplierL1 m f z*star (g z)) planeMeasure := by
  have hmeas := (variableFrequencyMultiplier_measurable_l1 m hm f hf).aestronglyMeasurable (μ:=planeMeasure)
  apply (hg.norm.const_mul ((∫ omega, q omega ∂planeMeasure)*(∫ x, ‖f x‖ ∂planeMeasure))).mono'
    (hmeas.mul hg.aestronglyMeasurable.star)
  filter_upwards [] with z
  change ‖variableFrequencyMultiplierL1 m f z*star (g z)‖≤_
  rw [norm_mul,norm_star]
  exact mul_le_mul_of_nonneg_right (variableFrequencyMultiplier_bound_l1 m q hq hbound f z) (norm_nonneg _)

theorem finite_variableFrequencyMultiplier_pairing_l1 {ι : Type*} [Fintype ι]
    (m : ι → (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : ∀ i, Measurable (m i))
    (q : ι → ℝ×ℝ → ℝ) (hq : ∀ i, Integrable (q i) planeMeasure)
    (hbound : ∀ i z omega, ‖m i (z,omega)‖≤q i omega)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure)
    (g : ℝ×ℝ → ℂ) (hg : Integrable g planeMeasure) :
    (∑ i, ∫ z, variableFrequencyMultiplierL1 (m i) f z*star (g z) ∂planeMeasure)=
      ∫ z, variableFrequencyMultiplierL1 (fun p => ∑ i, m i p) f z*star (g z) ∂planeMeasure := by
  classical
  rw [←integral_finsetSum _ (fun i _ =>
    variableFrequencyMultiplier_pairing_integrable_l1 (m i) (hm i) (q i) (hq i) (hbound i) f hf g hg)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [←Finset.sum_mul]
  congr 1
  unfold variableFrequencyMultiplierL1
  rw [←integral_finsetSum _ (fun i _ =>
    variableFrequencyMultiplier_integrand_integrable_l1 (m i) (hm i) (q i) (hq i) (hbound i) f hf z)]
  apply integral_congr_ae
  filter_upwards [] with omega
  simp only [Finset.sum_mul,Finset.smul_sum]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularFrequencyEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded direction and compact annular and vertical windows give a
single integrable frequency envelope, uniformly in the spatial point. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem annularBandSymbol_support_bounds
    (psi beta : SchwartzMap ℝ ℂ) (l W center M B U : ℝ)
    (hl : 0<l) (hW : 0<W) (hU : 0≤U)
    (hpsi : ∀ s, psi s≠0 → |s|≤M) (hbeta : ∀ s, beta s≠0 → |s|≤B)
    (u : ℝ×ℝ → ℝ) (hu : ∀ z, |u z|≤U) (z omega : ℝ×ℝ)
    (hp : psi (l*(omega.1+u z*omega.2))≠0)
    (hb : beta (symbolY W omega.2 center)≠0) :
    |omega.1|≤M/l+U*(|center|+B/W) ∧ |omega.2|≤|center|+B/W := by
  have hy := hbeta _ hb
  change |W*(omega.2-center)|≤B at hy
  rw [abs_mul,abs_of_pos hW] at hy
  have hy' : |omega.2-center|≤B/W := (le_div_iff₀ hW).mpr (by nlinarith)
  have hy'' : |omega.2|≤|center|+B/W := by
    calc
      |omega.2|=|(omega.2-center)+center| := by congr 1; ring
      _≤|omega.2-center|+|center| := abs_add_le _ _
      _≤|center|+B/W := by linarith
  have hx := hpsi _ hp
  rw [abs_mul,abs_of_pos hl] at hx
  have hx' : |omega.1+u z*omega.2|≤M/l := (le_div_iff₀ hl).mpr (by nlinarith)
  refine ⟨?_,hy''⟩
  calc
    |omega.1|=|(omega.1+u z*omega.2)-(u z*omega.2)| := by congr 1; ring
    _≤|omega.1+u z*omega.2|+|u z*omega.2| := abs_sub _ _
    _≤M/l+U*(|center|+B/W) := by
      rw [abs_mul]
      exact add_le_add hx' (mul_le_mul (hu z) hy'' (abs_nonneg _) hU)

theorem exists_frequency_rectangle_envelope
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (C R S : ℝ)
    (hbound : ∀ z omega, ‖m (z,omega)‖≤C)
    (hsupport : ∀ z omega, m (z,omega)≠0 → |omega.1|≤R ∧ |omega.2|≤S) :
    ∃ q : ℝ×ℝ → ℝ, Integrable q planeMeasure ∧
      ∀ z omega, ‖m (z,omega)‖≤q omega := by
  let s : Set (ℝ×ℝ) := Icc (-R) R ×ˢ Icc (-S) S
  have hs : MeasurableSet s := measurableSet_Icc.prod measurableSet_Icc
  have hfin : planeMeasure s≠∞ := (isCompact_Icc.prod isCompact_Icc).measure_ne_top
  refine ⟨s.indicator (fun _ => C), (integrableOn_const hfin).integrable_indicator hs,?_⟩
  intro z omega
  by_cases hm : m (z,omega)=0
  · have hC : 0≤C := (norm_nonneg (m (z,omega))).trans (hbound z omega)
    rw [hm,norm_zero]
    exact indicator_nonneg (fun _ _ => hC) _
  · have hmem : omega∈s := by
      obtain ⟨hR,hS⟩ := hsupport z omega hm
      exact ⟨abs_le.mp hR,abs_le.mp hS⟩
    rw [indicator_of_mem hmem]
    exact hbound z omega

theorem exists_partitionedFrequencySymbol_envelope
    (psi rho beta : SchwartzMap ℝ ℂ) (l W w theta center M B U : ℝ)
    (hl : 0<l) (hW : 0<W) (hU : 0≤U)
    (hpsi : ∀ s, psi s≠0 → |s|≤M) (hbeta : ∀ s, beta s≠0 → |s|≤B)
    (u : ℝ×ℝ → ℝ) (hu : ∀ z, |u z|≤U) :
    ∃ q : ℝ×ℝ → ℝ, Integrable q planeMeasure ∧
      ∀ z omega, ‖partitionedFrequencySymbol psi rho beta l W w theta center u (z,omega)‖≤q omega := by
  apply exists_frequency_rectangle_envelope _
    (SchwartzMap.seminorm ℝ 0 0 psi*SchwartzMap.seminorm ℝ 0 0 rho*SchwartzMap.seminorm ℝ 0 0 beta)
    (M/l+U*(|center|+B/W)) (|center|+B/W)
    (partitionedFrequencySymbol_bound psi rho beta l W w theta center u)
  intro z omega hm
  have hp : psi (l*(omega.1+u z*omega.2))≠0 := by
    intro hp; exact hm (by simp [partitionedFrequencySymbol,hp])
  have hb : beta (symbolY W omega.2 center)≠0 := by
    intro hb; exact hm (by simp [partitionedFrequencySymbol,hb])
  exact annularBandSymbol_support_bounds psi beta l W center M B U hl hW hU hpsi hbeta u hu z omega hp hb

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PartitionedFrequencyL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite slope recombination for L1 inputs, with all frequency
interchanges justified by the compact annular envelope. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem recombine_partitioned_frequency_pairing_l1 {ι : Type*} [Fintype ι]
    (psi rho beta : SchwartzMap ℝ ℂ) (l W w center M B U : ℝ) (theta : ι → ℝ)
    (hl : 0<l) (hW : 0<W)
    (hpsi : ∀ s, psi s≠0 → |s|≤M) (hbeta : ∀ s, beta s≠0 → |s|≤B)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (hub : ∀ z, |u z|≤U)
    (hpartition : ∀ z omega : ℝ×ℝ,
      psi (l*(omega.1+u z*omega.2))≠0 → beta (symbolY W omega.2 center)≠0 →
      ∑ i, rho (-symbolX l omega.1 omega.2 (theta i)/(w*omega.2))=1)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure)
    (g : ℝ×ℝ → ℂ) (hg : Integrable g planeMeasure) :
    (∑ i, ∫ z, variableFrequencyMultiplierL1
      (partitionedFrequencySymbol psi rho beta l W w (theta i) center u) f z*star (g z) ∂planeMeasure)=
      ∫ z, variableFrequencyMultiplierL1 (annularBandSymbol psi beta l W center u) f z*star (g z) ∂planeMeasure := by
  classical
  have henv (i : ι) := exists_partitionedFrequencySymbol_envelope psi rho beta
    l W w (theta i) center M B U hl hW ((abs_nonneg (u 0)).trans (hub 0)) hpsi hbeta u hub
  choose q hq hbound using henv
  rw [finite_variableFrequencyMultiplier_pairing_l1
    (fun i => partitionedFrequencySymbol psi rho beta l W w (theta i) center u)
    (fun i => partitionedFrequencySymbol_measurable psi rho beta l W w (theta i) center u hu)
    q hq hbound f hf g hg,
    sum_partitionedFrequencySymbol psi rho beta l W w center theta u hpartition]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_FiniteDiagonalBandL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arithmetic slope partition recombines exactly into the finite
vector-valued diagonal band operator. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem finitePartitionedBand_eq_diagonal_l1 {N : ℕ} {κ : Type} [Fintype κ]
    (psi beta : SchwartzMap ℝ ℂ) (K : Fin N → ℕ)
    (topLength width w delta c M B U : ℝ)
    (htop : 0<topLength) (hwidth : 0<width) (hw : 0<w) (hd : 0<delta) (hc : 0 < c) (hM : 0≤M)
    (hbetaSupport : ∀ s, beta s≠0 → |s|≤B)
    (center : κ → ℝ) (hpsi : ∀ s : ℝ, psi s≠0 → |s|≤M)
    (hbeta : ∀ k eta, beta (symbolY width eta (center k))≠0 → c≤w*eta)
    (hK : ∀ j, U/(delta*(w/(topLength/(2:ℝ)^j.val)))+M/(delta*c)≤K j)
    (u : ℝ×ℝ → ℝ) (hum : Measurable u) (hu : ∀ z, |u z|≤U)
    (f : κ → (ℝ×ℝ) → ℂ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : ∀ k, Integrable (f k) planeMeasure)
    (hg : ∀ k, Integrable (fun z => g z k) planeMeasure) :
    finitePartitionedBandL1 psi (scaledSlopePartition delta hd) beta topLength width w
      (fun j => finiteSlopeLabels (K j))
      (fun j n => finiteSlopeCenter (K j) delta (w/(topLength/(2:ℝ)^j.val)) n.val)
      center u f g=finiteDiagonalBandL1 (N:=N) psi beta topLength width center u f g := by
  classical
  unfold finitePartitionedBandL1 finiteDiagonalBandL1
  dsimp only [LatticeRow]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hlen : 0<topLength/(2:ℝ)^j.val := div_pos htop (pow_pos (by norm_num) _)
  exact recombine_partitioned_frequency_pairing_l1 psi (scaledSlopePartition delta hd) beta
    (topLength/(2:ℝ)^j.val) width w (center k) M B U
    (fun n : finiteSlopeLabels (K j) =>
      finiteSlopeCenter (K j) delta (w/(topLength/(2:ℝ)^j.val)) n.val) hlen hwidth hpsi hbetaSupport u hum hu
    (finiteSlopePartition_annular psi beta (K j) (topLength/(2:ℝ)^j.val) width w delta c M U
      (center k) hlen hw hd hc hM hpsi (hbeta k) (hK j) u hu) (f k) (hf k) (fun z => g z k) (hg k)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_FiniteDiagonalBasicL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform basic estimate for the actual finite diagonal band form.
Slope labels, plateaus, compact symbols, and profile budgets are all
constructed inside the proof. The scalar width W=w is included. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_finite_diagonal_basic_l1 (hVariation : LepingleInput)
    (psi beta : SchwartzMap ℝ ℂ) (A B c C a M delta : ℝ)
    (p : AnnularPacketGeometry A B c C a M) (hA : 0<A) (hB : 0<B)
    (hd : 0<delta) (hnarrow : delta*C≤A/2)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ K : ℝ, 0<K ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (topLength width w F : ℝ), 0<topLength → 0<width → 0<w → w≤width → 0≤F →
    ∀ (center : κ → ℝ), (∀ k, |2*Real.pi*center k|≤F/w) →
      (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f : κ → (ℝ×ℝ) → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
      (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      planeMeasure E≠∞ → planeMeasure Fset≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center u f g‖≤
        K*Real.sqrt (planeMeasure.real Fset)*Real.sqrt (planeMeasure.real E) := by
  let p' := p.enlargeVertical
  let beta' := verticallyRescaledWindow beta p.H p.H_pos
  let chi := rectangularFrequencyCutoff A (p.H*B) hA (mul_pos p.H_pos hB)
  obtain ⟨multiplicity,hmult⟩ := exists_finiteSlopeCenter_multiplicity delta p.H hd p.H_pos.le
  obtain ⟨K,hK,hmain⟩ := exists_partitioned_annular_basic_l1 hVariation psi
    (scaledSlopePartition delta hd) beta' chi chi A (p.H*B) c C a M p' multiplicity
    hpsi (rectangularFrequencyCutoff_support A (p.H*B) hA (mul_pos p.H_pos hB))
    (rectangularFrequencyCutoff_support A (p.H*B) hA (mul_pos p.H_pos hB))
  refine ⟨K,hK,?_⟩
  intro N κ _ topLength width w F htop hwidth hw hwW hF center hfrequency hlo hhi
    u hum hu f fData g hf hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hgs hfs
  have hfint : ∀ k, Integrable (f k) planeMeasure := by
    intro k
    exact (bounded_supported_coordinate_integrable fData hfm hfb Fset hFset hFfin hfs k).congr
      (Filter.Eventually.of_forall (fun z => (hf z k).symm))
  let Krow (j : Fin N) : ℕ := ⌈1/(delta*(w/(topLength/(2:ℝ)^j.val)))+M/(delta*c)⌉₊
  let labels := fun j : Fin N => finiteSlopeLabels (Krow j)
  let theta := fun (j : Fin N) (n : labels j) =>
    finiteSlopeCenter (Krow j) delta (w/(topLength/(2:ℝ)^j.val)) n.val
  have hlocal (j : Fin N) : SourceSlopeLabels.LocalMultiplicity Finset.univ (theta j)
      ((p.H*w)/(topLength/(2:ℝ)^j.val)) multiplicity := by
    simpa only [theta,mul_div_assoc] using hmult (Krow j) (w/(topLength/(2:ℝ)^j.val))
      (div_pos hw (div_pos htop (pow_pos (by norm_num) _)))
  have hscale (k : κ) : |2*Real.pi*center k|≤(p.H*F)/(p.H*w) := by
    rw [mul_div_mul_left F w p.H_pos.ne']
    exact hfrequency k
  have hpad : (p.H*B)*(w/(p.H*width))=B*(w/width) := by field_simp [p.H_pos.ne',hwidth.ne']
  have hlo' (k : κ) : c+(p.H*B)*(w/(p.H*width))≤w*center k := by rw [hpad]; exact hlo k
  have hhi' (k : κ) : w*center k+(p.H*B)*(w/(p.H*width))≤C := by rw [hpad]; exact hhi k
  have hout := hmain N κ (fun _ : Fin N => ℕ) topLength (p.H*width) w (p.H*F)
    htop (mul_pos p.H_pos hwidth) hw (mul_le_mul_of_nonneg_left hwW p.H_pos.le)
    (mul_nonneg p.H_pos.le hF) labels theta center hscale hlo' hhi' hlocal
    u hum f fData g hfint hf hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hgs hfs
  rw [partitionedAnnularSum_eq_finitePartitionedBand_l1 psi beta' A (p.H*B) c C delta
    hA (mul_pos p.H_pos hB) p.hc hd hnarrow
    (verticallyRescaledWindow_support beta B p.H p.H_pos hbeta)
    topLength (p.H*width) w htop (mul_pos p.H_pos hwidth) hw labels theta center
    hlo' hhi' u f g] at hout
  rw [finitePartitionedBand_vertical_rescaling_l1 psi (scaledSlopePartition delta hd) beta
    p.H p.H_pos topLength width w labels theta center u f g] at hout
  have hbetaband (k : κ) (eta : ℝ) (hb : beta (symbolY width eta (center k))≠0) : c≤w*eta := by
    exact (vertical_annulus_from_window w width (center k) eta B c C hw hwidth
      (hlo k) (hhi k) ((hbeta _ hb).trans (by linarith))).1
  rw [finitePartitionedBand_eq_diagonal_l1 psi beta Krow topLength width w delta c M (B/2) 1
    htop hwidth hw hd p.hc p.hM.le hbeta center (fun s hs => (hpsi s hs).2) hbetaband
    (fun j => Nat.le_ceil _) u hum hu f g hfint
    (bounded_supported_coordinate_integrable g hgm hgb E hE hEfin hgs)] at hout
  exact hout

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_BandDiagonalBasicL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The basic diagonal estimate with only the original annular support
and bin hypotheses. All packet geometry is constructed internally. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem band_diagonal_basic_l1 (hVariation : LepingleInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ K : ℝ, 0<K ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (topLength width w : ℝ), 0<topLength → 0<width → 0<w → w≤width →
    ∀ (center : κ → ℝ), (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f : κ → (ℝ×ℝ) → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
      (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      planeMeasure E≠∞ → planeMeasure Fset≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center u f g‖≤
        K*Real.sqrt (planeMeasure.real Fset)*Real.sqrt (planeMeasure.real E) := by
  obtain ⟨A,delta,p,hA,hd,hnarrow⟩ := exists_diagonal_geometry B c C a M hB hc hC ha hM
  obtain ⟨K,hK,hmain⟩ := exists_finite_diagonal_basic_l1 hVariation psi beta A B c C a M delta
    p hA hB hd hnarrow hpsi hbeta
  refine ⟨K,hK,?_⟩
  intro N κ _ topLength width w htop hwidth hw hwW center hlo hhi
    u hum hu f fData g hf hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hgs hfs
  exact hmain N κ topLength width w (2*Real.pi*C) htop hwidth hw hwW (by positivity)
    center (fun k => (center_frequency_bounds B c C w width (center k) hB.le hc hw hwidth (hlo k) (hhi k)).2)
    hlo hhi u hum hu f fData g hf hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hgs hfs

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularBandL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem annularBandSymbol_measurable (psi beta : SchwartzMap ℝ ℂ)
    (l W center : ℝ) (u : ℝ×ℝ → ℝ) (hu : Measurable u) :
    Measurable (annularBandSymbol psi beta l W center u) := by
  have hu' : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => u p.1) := hu.comp measurable_fst
  unfold annularBandSymbol symbolY
  apply Measurable.mul
  · apply psi.continuous.measurable.comp
    fun_prop
  · apply beta.continuous.measurable.comp
    fun_prop

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularBinMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The annular symbol with the enlarged bin plateau is exactly the time
kernel acting on the true bin projection. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem slopeKernelOperator_finiteTimeKernel (k : SchwartzMap ℝ ℂ) (N : ℕ)
    (topLength : ℝ) (htop : 0<topLength) (u : (ℝ×ℝ) → ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    slopeKernelOperator (finiteTimeKernel k N topLength) u f z=
      ∑ j : Fin N, slopeKernelOperator (scaledTimeKernel k (topLength/(2:ℝ)^j.val)) u f z := by
  have hi (j : Fin N) : Integrable (fun t =>
      scaledTimeKernel k (topLength/(2:ℝ)^j.val) t*f (z.1-t,z.2-t*u z)) := by
    have hk := scaledTimeKernel_integrable k k.integrable (topLength/(2:ℝ)^j.val)
      (ne_of_gt (div_pos htop (pow_pos (by norm_num) _)))
    apply (hk.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 f)).mono'
    · exact hk.aestronglyMeasurable.mul (f.continuous.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards [] with t
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f _) (norm_nonneg _)
  unfold slopeKernelOperator finiteTimeKernel
  simp only [Finset.sum_mul]
  exact integral_finsetSum _ (fun j _ => hi j)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedBandProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed normalization of the original vertical cutoff controls its
L1, L2 and uniform sizes without changing its frequency band or strip. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem verticalProjectionCost_pos (p : SchwartzMap ℝ ℂ) : 0<verticalProjectionCost p := by
  unfold verticalProjectionCost
  have h : 0≤∫ s, ‖(𝓕⁻ p : SchwartzMap ℝ ℂ) s‖ := integral_nonneg fun _ => norm_nonneg _
  linarith

theorem normalizedBandProjection_apply (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (hw : 0<w) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    normalizedBandProjection p w f z=((verticalProjectionCost p)⁻¹ : ℂ)*
      verticalConvolution (verticalProfileKernel p w 0) f z := by
  change ((verticalProjectionCost p)⁻¹ : ℂ)*schwartzVerticalProjection p w 0 f z=_
  rw [schwartzVerticalProjection_eq_convolution p w 0 hw]

theorem normalizedBandProjection_sizes (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (hw : 0<w) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    (∫ z, ‖normalizedBandProjection p w f z‖ ∂planeMeasure)≤∫ z, ‖f z‖ ∂planeMeasure ∧
      (∫ z, ‖normalizedBandProjection p w f z‖^2 ∂planeMeasure)≤∫ z, ‖f z‖^2 ∂planeMeasure := by
  let K := verticalProfileKernel p w 0
  let A := ∫ s, ‖(𝓕⁻ p : SchwartzMap ℝ ℂ) s‖
  let C := verticalProjectionCost p
  have hC : 0<C := verticalProjectionCost_pos p
  have hA : 0≤A := integral_nonneg fun _ => norm_nonneg _
  have hAC : C⁻¹*A≤1 := by
    rw [mul_comm,←div_eq_mul_inv]
    apply (div_le_one hC).2
    change A≤1+A
    linarith
  have hKm : Measurable K := by
    unfold K verticalProfileKernel modulatedTimeKernel scaledTimeKernel
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (continuous_const.mul ((𝓕⁻ p : SchwartzMap ℝ ℂ).continuous.comp (by fun_prop)))).measurable
  have hKi : Integrable K := modulatedTimeKernel_integrable (𝓕⁻ p) w 0 hw
  have hKnorm : (∫ s, ‖K s‖)=A := modulatedTimeKernel_l1 (𝓕⁻ p) w 0 hw
  have hn (z) : ‖normalizedBandProjection p w f z‖=C⁻¹*‖verticalConvolution K f z‖ := by
    rw [normalizedBandProjection_apply p w hw,norm_mul]
    simp only [C,K,norm_inv,Complex.norm_real,Real.norm_of_nonneg (verticalProjectionCost_pos p).le]
  have h1 := verticalConvolution_l1_bound K hKi hKm f f.continuous.measurable f.integrable
  have h2 := (verticalConvolution_energy_bound K hKi hKm f f.continuous.measurable
    (f.memLp 2 planeMeasure)).2
  rw [hKnorm] at h1 h2
  constructor
  · simp_rw [hn]
    rw [integral_const_mul]
    calc
      _ ≤ C⁻¹*(A*∫ z, ‖f z‖ ∂planeMeasure) := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hC.le)
      _ ≤ ∫ z, ‖f z‖ ∂planeMeasure := by
        rw [←mul_assoc]
        exact mul_le_of_le_one_left (integral_nonneg fun _ => norm_nonneg _) hAC
  · simp_rw [hn,mul_pow]
    rw [integral_const_mul]
    calc
      _ ≤ (C⁻¹)^2*(A^2*∫ z, ‖f z‖^2 ∂planeMeasure) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ ≤ ∫ z, ‖f z‖^2 ∂planeMeasure := by
        rw [←mul_assoc,←mul_pow]
        exact mul_le_of_le_one_left (integral_nonneg fun _ => sq_nonneg _)
          (by nlinarith [pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr hC.le) hA) hAC 2])

theorem normalizedBandProjection_uniform (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (hw : 0<w) (f : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1) :
    ∀ z, ‖normalizedBandProjection p w f z‖≤1 := by
  intro z
  rw [normalizedBandProjection_apply p w hw,norm_mul]
  have hC := verticalProjectionCost_pos p
  simp only [norm_inv,Complex.norm_real,Real.norm_of_nonneg hC.le]
  have h := verticalConvolution_uniform_bound (verticalProfileKernel p w 0)
    (modulatedTimeKernel_integrable (𝓕⁻ p) w 0 hw) f 1 hf z
  rw [one_mul,show (∫ s, ‖verticalProfileKernel p w 0 s‖)=
    (∫ s, ‖(𝓕⁻ p : SchwartzMap ℝ ℂ) s‖) from modulatedTimeKernel_l1 _ w 0 hw] at h
  apply (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hC.le)).trans
  rw [mul_comm,←div_eq_mul_inv]
  apply (div_le_one hC).2
  unfold verticalProjectionCost
  linarith

theorem normalizedBandProjection_support (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (S : Set ℝ) (hf : ∀ z, z.1∉S → f z=0) :
    ∀ z, z.1∉S → normalizedBandProjection p w f z=0 := by
  intro z hz
  rw [normalizedBandProjection_apply p w hw,verticalConvolution_horizontal_support _ f S hf z hz,mul_zero]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HorizontalHilbertPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricted horizontal estimates at the two exponents used in the
manuscript, transferred to the original vertical cutoff. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem schwartz_power_le_l1 (f : SchwartzMap (ℝ×ℝ) ℂ)
    (hf : ∀ z, ‖f z‖≤1) (p : ℝ) (hp : 1≤p) :
    (∫ z, ‖f z‖^p ∂planeMeasure)≤∫ z, ‖f z‖ ∂planeMeasure := by
  have hp0 : 0<p := lt_of_lt_of_le zero_lt_one hp
  have hi : Integrable (fun z => ‖f z‖^p) planeMeasure := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      (f.memLp (ENNReal.ofReal p) planeMeasure).integrable_norm_rpow
        (by simpa only [ne_eq,ENNReal.ofReal_eq_zero,not_le] using hp0) (by simp)
  exact integral_mono hi (f.integrable.norm) fun z =>
    Real.rpow_le_self_of_le_one (norm_nonneg _) (hf z) hp

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HilbertTimeDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assembly of the actual short, middle and long time pieces. The
middle term is the finite annular operator already estimated by the
packet argument; all other terms have explicit restricted bounds. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem kernelPairing_projection_normalize (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (p : SchwartzMap ℝ ℂ) (w : ℝ) (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    kernelPairing K u (schwartzVerticalProjection p w 0 f) g=
      (verticalProjectionCost p : ℂ)*kernelPairing K u (normalizedBandProjection p w f) g := by
  have heq : schwartzVerticalProjection p w 0 f=
      (verticalProjectionCost p : ℂ) • normalizedBandProjection p w f := by
    unfold normalizedBandProjection
    rw [smul_smul,mul_inv_cancel₀ (by exact_mod_cast (verticalProjectionCost_pos p).ne' :
      (verticalProjectionCost p : ℂ)≠0),one_smul]
  rw [heq,kernelPairing_smul]

theorem hilbertProjected_middle_error :
    ∃ B : ℝ, 0≤B ∧ ∀ s T : ℝ, 0 < s → s≤T →
      ∃ N : ℕ, s≤T/(2:ℝ)^N ∧ T/(2:ℝ)^N<2*s ∧
      ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u →
      ∀ (p : SchwartzMap ℝ ℂ) (w : ℝ), 0<w →
      ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      ∀ l r : ℝ, r-l≤1/4 → (∀ z, z.1∉Icc l r → f z=0) →
        (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel s T) u (schwartzVerticalProjection p w 0 f) g-
        kernelPairing (finiteTimeKernel hilbertTimeKernel N (T/2)) u
          (schwartzVerticalProjection p w 0 f) g‖≤
        (verticalProjectionCost p*B)*
          min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
  obtain ⟨B,hB,hmain⟩ := hilbertArbitraryEndpoint_pairing
  refine ⟨B,hB,?_⟩
  intro s T hs hsT
  obtain ⟨N,hlo,hhi,hbound⟩ := hmain s T hs hsT
  refine ⟨N,hlo,hhi,?_⟩
  intro u hu p w hw f g hf hg l r hwidth hfstrip hgstrip
  have hb := hbound u hu (normalizedBandProjection p w f) g
    (normalizedBandProjection_uniform p w hw f hf) hg l r hwidth
    (normalizedBandProjection_support p w hw f _ hfstrip) hgstrip
  have hsize := (normalizedBandProjection_sizes p w hw f).1
  rw [kernelPairing_projection_normalize,kernelPairing_projection_normalize,←mul_sub,norm_mul,
    Complex.norm_real,Real.norm_of_nonneg (verticalProjectionCost_pos _).le]
  calc
    _ ≤ verticalProjectionCost p*(B*min
        (4*∫ z, ‖normalizedBandProjection p w f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)) :=
      mul_le_mul_of_nonneg_left hb (verticalProjectionCost_pos _).le
    _ ≤ verticalProjectionCost p*(B*min
        (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)) := by
      apply mul_le_mul_of_nonneg_left _ (verticalProjectionCost_pos _).le
      exact mul_le_mul_of_nonneg_left
        (min_le_min (mul_le_mul_of_nonneg_left hsize (by norm_num)) le_rfl) hB
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RestrictedTestApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded measurable restricted tests admit unit-bounded Schwartz
approximants in every open neighbourhood of their finite-measure support. -/
noncomputable section
open MeasureTheory Function Set
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem restrictedTest_integrable (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f)
    (hb : ∀ z, ‖f z‖≤1) (A : Set (ℝ×ℝ)) (hA : MeasurableSet A)
    (hAfin : planeMeasure A≠∞) (hsupp : support f⊆A) : Integrable f planeMeasure := by
  have hi : Integrable (A.indicator (fun _ : ℝ×ℝ => (1:ℝ))) planeMeasure :=
    (integrableOn_const hAfin).integrable_indicator hA
  apply hi.mono' hfm.aestronglyMeasurable
  filter_upwards [] with z
  by_cases hz : z∈A
  · simpa only [Set.indicator_of_mem hz] using hb z
  · have hzero : f z=0 := notMem_support.mp (fun h => hz (hsupp h))
    simp only [Set.indicator_of_notMem hz,hzero,norm_zero,le_refl]

theorem restrictedTest_cutoff_pointwise (f : (ℝ×ℝ) → ℂ)
    (hb : ∀ z, ‖f z‖≤1) (A K : Set (ℝ×ℝ)) (hsupp : support f⊆A) (z : ℝ×ℝ) :
    ‖K.indicator f z-f z‖^2≤(A\K).indicator (fun _ : ℝ×ℝ => (1:ℝ)) z := by
  by_cases hzK : z∈K
  · simp only [Set.indicator_of_mem hzK,sub_self,norm_zero,zero_pow (by decide : 2≠0)]
    exact indicator_nonneg (fun _ _ => by norm_num) _
  · rw [Set.indicator_of_notMem hzK]
    by_cases hzA : z∈A
    · rw [Set.indicator_of_mem (show z∈A\K from ⟨hzA,hzK⟩)]
      simpa only [zero_sub,norm_neg,one_pow] using
        pow_le_pow_left₀ (norm_nonneg _) (hb z) 2
    · have hzero : f z=0 := notMem_support.mp (fun h => hzA (hsupp h))
      simp only [hzero,sub_self,norm_zero,zero_pow (by decide : 2≠0)]
      exact indicator_nonneg (fun _ _ => by norm_num) _

theorem restrictedTest_compact_integral_error (f : (ℝ×ℝ) → ℂ)
    (hb : ∀ z, ‖f z‖≤1) (hf2 : MemLp f 2 planeMeasure)
    (A K : Set (ℝ×ℝ)) (hA : MeasurableSet A) (hAfin : planeMeasure A≠∞)
    (hK : MeasurableSet K) (hsupp : support f⊆A) :
    (∫ z, ‖K.indicator f z-f z‖^2 ∂planeMeasure)≤planeMeasure.real (A\K) := by
  have hdiff : MeasurableSet (A\K) := hA.diff hK
  have hdiffFin : planeMeasure (A\K)≠∞ :=
    ne_top_of_le_ne_top hAfin (measure_mono sdiff_subset)
  have hi : Integrable ((A\K).indicator (fun _ : ℝ×ℝ => (1:ℝ))) planeMeasure :=
    (integrableOn_const hdiffFin).integrable_indicator hdiff
  have hierr : Integrable (fun z => ‖K.indicator f z-f z‖^2) planeMeasure :=
    (memLp_two_iff_integrable_sq_norm ((hf2.indicator hK).sub hf2).aestronglyMeasurable).mp
      ((hf2.indicator hK).sub hf2)
  calc
    _ ≤ ∫ z, (A\K).indicator (fun _ : ℝ×ℝ => (1:ℝ)) z ∂planeMeasure :=
      integral_mono hierr hi (restrictedTest_cutoff_pointwise f hb A K hsupp)
    _ = _ := by simpa only [smul_eq_mul,mul_one] using integral_indicator_const (1:ℝ) hdiff

theorem restrictedTest_compact_error (f : (ℝ×ℝ) → ℂ)
    (hb : ∀ z, ‖f z‖≤1) (hf2 : MemLp f 2 planeMeasure)
    (A K : Set (ℝ×ℝ)) (hA : MeasurableSet A) (hAfin : planeMeasure A≠∞)
    (hK : MeasurableSet K) (hsupp : support f⊆A) :
    ‖(hf2.indicator hK).toLp (K.indicator f)-hf2.toLp f‖^2≤planeMeasure.real (A\K) := by
  have heq := MemLp.toLp_sub (f:=K.indicator f) (g:=f) (hf2.indicator hK) hf2
  rw [←heq,memLp_toL2_norm_sq]
  exact restrictedTest_compact_integral_error f hb hf2 A K hA hAfin hK hsupp

theorem exists_schwartz_approx_restricted (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f)
    (hb : ∀ z, ‖f z‖≤1) (hf2 : MemLp f 2 planeMeasure)
    (A U : Set (ℝ×ℝ)) (hA : MeasurableSet A) (hAfin : planeMeasure A≠∞)
    (hsupp : support f⊆A) (hU : IsOpen U) (hAU : A⊆U) (epsilon : ℝ) (he : 0<epsilon) :
    ∃ g : SchwartzMap (ℝ×ℝ) ℂ, (∀ z, ‖g z‖≤1) ∧ support g⊆U ∧
      ‖g.toLp 2 planeMeasure-hf2.toLp f‖<epsilon := by
  have hehalf : 0<epsilon/2 := by positivity
  obtain ⟨K,hKA,hK,herror⟩ := hA.exists_isCompact_sdiff_lt hAfin
    (by positivity : ENNReal.ofReal ((epsilon/2)^2)≠0)
  have hf := restrictedTest_integrable f hfm hb A hA hAfin hsupp
  let fK := K.indicator f
  have hfKm : Measurable fK := hfm.indicator hK.measurableSet
  have hfKi : Integrable fK planeMeasure := hf.indicator hK.measurableSet
  have hfK2 : MemLp fK 2 planeMeasure := hf2.indicator hK.measurableSet
  have hfKs : support fK⊆K := by
    intro z hz
    by_contra hn
    exact hz (Set.indicator_of_notMem hn f)
  have hfKc : HasCompactSupport fK := hK.of_isClosed_subset isClosed_closure
    (closure_minimal (hfKs) hK.isClosed)
  have hfKb (z) : ‖fK z‖≤1 := by
    by_cases hz : z∈K
    · simpa only [fK,Set.indicator_of_mem hz] using hb z
    · simp only [fK,Set.indicator_of_notMem hz,norm_zero,zero_le_one]
  have hKfin : planeMeasure (A\K)≠∞ := ne_top_of_le_ne_top hAfin (measure_mono sdiff_subset)
  have herrReal : planeMeasure.real (A\K)<(epsilon/2)^2 := by
    exact (ENNReal.toReal_lt_toReal hKfin ENNReal.ofReal_ne_top).2 herror |>.trans_eq
      (ENNReal.toReal_ofReal (sq_nonneg _))
  have hnorm : ‖hfK2.toLp fK-hf2.toLp f‖<epsilon/2 := by
    have hsquare := (restrictedTest_compact_error f hb hf2 A K hA hAfin hK.measurableSet hsupp).trans_lt herrReal
    exact (sq_lt_sq₀ (norm_nonneg _) hehalf.le).1 hsquare
  obtain ⟨g,hgb,hgs,hgclose⟩ := exists_schwartz_approx_compact fK hfKm hfKi hfKc hfKb hfK2
    K U hK (hfKs) hU (hKA.trans hAU) (epsilon/2) hehalf
  refine ⟨g,hgb,hgs,?_⟩
  have htri := norm_add_le (g.toLp 2 planeMeasure-hfK2.toLp fK) (hfK2.toLp fK-hf2.toLp f)
  rw [sub_add_sub_cancel] at htri
  linarith only [htri,hgclose,hnorm]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RestrictedTestOpenApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded Schwartz approximation with support measures converging to
the original measurable support, inside a fixed open ambient set. -/
noncomputable section
open MeasureTheory Function Set Filter
open scoped ENNReal Topology
namespace LipschitzHilbert.PacketRepresentation

theorem exists_open_approx_inside (A V : Set (ℝ×ℝ))
    (hAfin : planeMeasure A≠∞) (hV : IsOpen V) (hAV : A⊆V)
    (epsilon : ℝ) (he : 0<epsilon) :
    ∃ U : Set (ℝ×ℝ), IsOpen U ∧ A⊆U ∧ U⊆V ∧ planeMeasure U≠∞ ∧
      planeMeasure.real A≤planeMeasure.real U ∧
      planeMeasure.real U<planeMeasure.real A+epsilon := by
  obtain ⟨O,hAO,hO,hOm⟩ := A.exists_isOpen_lt_add (μ:=planeMeasure) hAfin
    (by positivity : ENNReal.ofReal epsilon≠0)
  have hOfin : planeMeasure O≠∞ := ne_top_of_lt
    (hOm.trans_le (le_of_lt (ENNReal.add_lt_top.mpr ⟨hAfin.lt_top,ENNReal.ofReal_lt_top⟩)))
  let U := O∩V
  have hAU : A⊆U := fun _ hz => ⟨hAO hz,hAV hz⟩
  have hUfin : planeMeasure U≠∞ := ne_top_of_le_ne_top hOfin (measure_mono inter_subset_left)
  have hupper : planeMeasure.real O<planeMeasure.real A+epsilon := by
    have ht := (ENNReal.toReal_lt_toReal hOfin (ENNReal.add_ne_top.mpr ⟨hAfin,ENNReal.ofReal_ne_top⟩)).2 hOm
    simpa only [Measure.real,ENNReal.toReal_add hAfin ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal he.le] using ht
  exact ⟨U,hO.inter hV,hAU,inter_subset_right,hUfin,
    measureReal_mono hAU hUfin,(measureReal_mono inter_subset_left hOfin).trans_lt hupper⟩

theorem exists_schwartz_open_approx (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f)
    (hb : ∀ z, ‖f z‖≤1) (hf2 : MemLp f 2 planeMeasure)
    (A V : Set (ℝ×ℝ)) (hA : MeasurableSet A) (hAfin : planeMeasure A≠∞)
    (hsupp : support f⊆A) (hV : IsOpen V) (hfsV : support f⊆V) (epsilon : ℝ) (he : 0<epsilon) :
    ∃ (g : SchwartzMap (ℝ×ℝ) ℂ) (U : Set (ℝ×ℝ)),
      (∀ z, ‖g z‖≤1) ∧ support g⊆U ∧ IsOpen U ∧ A⊆U ∧ support g⊆V ∧
      planeMeasure U≠∞ ∧ planeMeasure.real A≤planeMeasure.real U ∧
      planeMeasure.real U<planeMeasure.real A+epsilon ∧
      ‖g.toLp 2 planeMeasure-hf2.toLp f‖<epsilon := by
  obtain ⟨U,hU,hAU,_,hUfin,hUlo,hUhi⟩ := exists_open_approx_inside A univ hAfin isOpen_univ (subset_univ A) epsilon he
  have hAVfin : planeMeasure (A∩V)≠∞ := ne_top_of_le_ne_top hAfin (measure_mono inter_subset_left)
  obtain ⟨g,hgb,hgs,hgn⟩ := exists_schwartz_approx_restricted f hfm hb hf2
    (A∩V) (U∩V) (hA.inter hV.measurableSet) hAVfin (subset_inter hsupp hfsV)
    (hU.inter hV) (inter_subset_inter_left V hAU) epsilon he
  exact ⟨g,U,hgb,hgs.trans inter_subset_left,hU,hAU,hgs.trans inter_subset_right,
    hUfin,hUlo,hUhi,hgn⟩

theorem exists_schwartz_open_approx_sequence (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f)
    (hb : ∀ z, ‖f z‖≤1) (hf2 : MemLp f 2 planeMeasure)
    (A V : Set (ℝ×ℝ)) (hA : MeasurableSet A) (hAfin : planeMeasure A≠∞)
    (hsupp : support f⊆A) (hV : IsOpen V) (hfsV : support f⊆V) :
    ∃ (g : ℕ → SchwartzMap (ℝ×ℝ) ℂ) (U : ℕ → Set (ℝ×ℝ)),
      (∀ n, (∀ z, ‖g n z‖≤1) ∧ support (g n)⊆U n ∧ IsOpen (U n) ∧
        A⊆U n ∧ support (g n)⊆V ∧ planeMeasure (U n)≠∞) ∧
      Tendsto (fun n => (g n).toLp 2 planeMeasure) atTop (𝓝 (hf2.toLp f)) ∧
      Tendsto (fun n => planeMeasure.real (U n)) atTop (𝓝 (planeMeasure.real A)) := by
  have he (n : ℕ) : 0<(1:ℝ)/((n:ℝ)+1) := by positivity
  choose g U hgb hgs hU hAU hUV hUfin hUlo hUhi hgn using
    (fun n : ℕ => exists_schwartz_open_approx f hfm hb hf2 A V hA hAfin hsupp hV hfsV
      ((1:ℝ)/((n:ℝ)+1)) (he n))
  refine ⟨g,U,(fun n => ⟨hgb n,hgs n,hU n,hAU n,hUV n,hUfin n⟩),?_,?_⟩
  · apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    simpa only [dist_eq_norm] using (hgn n).le
  · have hup : Tendsto (fun n : ℕ => planeMeasure.real A+1/((n:ℝ)+1))
        atTop (𝓝 (planeMeasure.real A)) := by
      simpa only [add_zero] using
        (tendsto_const_nhds (x:=planeMeasure.real A)).add tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup hUlo (fun n => (hUhi n).le)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RestrictedLogDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing a logarithmic restricted estimate from bounded Schwartz
functions to measurable bounded tests, preserving the support masses. -/
noncomputable section
open Set MeasureTheory Filter Function
open scoped ENNReal Topology
namespace LipschitzHilbert.PacketRepresentation

theorem restrictedLogFactor_tendsto (C : ℝ) (a b : ℕ → ℝ) (A B : ℝ)
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B)) (hA : 0<A) (hB : 0<B) :
    Tendsto (fun n => restrictedLogFactor C (a n) (b n)) atTop (𝓝 (restrictedLogFactor C A B)) := by
  have hlog := (ha.div hb hB.ne').log (div_ne_zero hA.ne' hB.ne')
  have hden : (1+|Real.log (A/B)|)^3≠0 := by positivity
  have hinv : Tendsto (fun n => ((1+|Real.log (a n/b n)|)^3)⁻¹) atTop
      (𝓝 (((1+|Real.log (A/B)|)^3)⁻¹)) :=
    (((tendsto_const_nhds (x:=(1:ℝ))).add hlog.abs).pow 3).inv₀ hden
  exact ((tendsto_const_nhds.mul hinv).mul ha.sqrt).mul hb.sqrt

theorem restricted_log_density (B : Lp ℂ 2 planeMeasure →L[ℝ] Lp ℂ 2 planeMeasure →L[ℝ] ℂ)
    (C : ℝ) (V : Set (ℝ×ℝ)) (hV : IsOpen V)
    (hbound : ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ),
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) → support f⊆V → support g⊆V →
      ∀ F G : Set (ℝ×ℝ), MeasurableSet F → MeasurableSet G →
        planeMeasure F≠∞ → planeMeasure G≠∞ → 0<planeMeasure.real F → 0<planeMeasure.real G →
        support f⊆F → support g⊆G →
        ‖B (f.toLp 2 planeMeasure) (g.toLp 2 planeMeasure)‖≤
          restrictedLogFactor C (planeMeasure.real F) (planeMeasure.real G))
    (f g : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ z, ‖f z‖≤1) (hg : ∀ z, ‖g z‖≤1)
    (hfV : support f⊆V) (hgV : support g⊆V)
    (F G : Set (ℝ×ℝ)) (hF : MeasurableSet F) (hG : MeasurableSet G)
    (hFfin : planeMeasure F≠∞) (hGfin : planeMeasure G≠∞)
    (hFpos : 0<planeMeasure.real F) (hGpos : 0<planeMeasure.real G)
    (hfs : support f⊆F) (hgs : support g⊆G)
    (hf2 : MemLp f 2 planeMeasure) (hg2 : MemLp g 2 planeMeasure) :
    ‖B (hf2.toLp f) (hg2.toLp g)‖ ≤ restrictedLogFactor C (planeMeasure.real F) (planeMeasure.real G) := by
  obtain ⟨fn,Fn,hfn,hflim,hFmass⟩ := exists_schwartz_open_approx_sequence f hfm hf hf2 F V hF hFfin hfs hV hfV
  obtain ⟨gn,Gn,hgn,hglim,hGmass⟩ := exists_schwartz_open_approx_sequence g hgm hg hg2 G V hG hGfin hgs hV hgV
  have hlim := (B.isBoundedBilinearMap.continuous.tendsto _).comp (hflim.prodMk_nhds hglim)
  have hright := restrictedLogFactor_tendsto C _ _ _ _ hFmass hGmass hFpos hGpos
  apply le_of_tendsto_of_tendsto hlim.norm hright
  filter_upwards [] with n
  rcases hfn n with ⟨hfnb,hfns,hFn,hFFn,hfnV,hFnfin⟩
  rcases hgn n with ⟨hgnb,hgns,hGn,hGGn,hgnV,hGnfin⟩
  exact hbound (fn n) (gn n) hfnb hgnb hfnV hgnV (Fn n) (Gn n) hFn.measurableSet hGn.measurableSet
    hFnfin hGnfin (hFpos.trans_le (measureReal_mono hFFn hFnfin))
    (hGpos.trans_le (measureReal_mono hGGn hGnfin)) hfns hgns

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RestrictedLogNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary uniform logarithmic weights for the three restricted
regimes. The exponential estimate is global and uses 1+x <= exp x. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem exponential_log_weight (b : ℝ) (hb : 0<b) :
    ∃ C : ℝ, 0<C ∧ ∀ x : ℝ, 0≤x →
      Real.exp (-b*x)≤C*((1+x)^3)⁻¹ := by
  let M := 1+3/b
  have hM : 0<M := by dsimp [M]; positivity
  refine ⟨M^3,pow_pos hM _,?_⟩
  intro x hx
  have hfirst : 1+x≤M*Real.exp (b*x/3) := by
    calc
      1+x ≤ 1+3/b+x+b*x/3 := by
        have h1 : 0≤3/b := by positivity
        have h2 : 0≤b*x/3 := by positivity
        linarith only [h1,h2]
      _ = M*(1+b*x/3) := by dsimp [M]; field_simp; ring
      _ ≤ M*Real.exp (b*x/3) := mul_le_mul_of_nonneg_left
        (by simpa only [add_comm] using Real.add_one_le_exp (b*x/3)) hM.le
  have hp := pow_le_pow_left₀ (by positivity : 0≤1+x) hfirst 3
  have hexp : (Real.exp (b*x/3))^3=Real.exp (b*x) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  rw [mul_pow,hexp] at hp
  have hprod : Real.exp (-b*x)*(1+x)^3≤M^3 := by
    calc
      _ ≤ Real.exp (-b*x)*(M^3*Real.exp (b*x)) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
      _ = _ := by rw [mul_left_comm,←Real.exp_add]; simp
  rw [←div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity : 0<(1+x)^3)).2 hprod

theorem high_log_weight (L : ℝ) (hL : 1≤L) :
    L^(-19:ℝ)≤27*((1+2*L)^3)⁻¹ := by
  have hLp : 0<L := zero_lt_one.trans_le hL
  calc
    L^(-19:ℝ) ≤ L^(-3:ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    _ = 1/L^3 := by rw [Real.rpow_neg hLp.le]; norm_num [Real.rpow_natCast,one_div]
    _ ≤ 27/(1+2*L)^3 := by
      apply (div_le_div_iff₀ (pow_pos hLp _) (by positivity)).2
      have h := pow_le_pow_left₀ (by positivity : 0≤1+2*L)
        (show 1+2*L≤3*L by linarith only [hL]) 3
      simpa only [one_mul,mul_pow,show (3:ℝ)^3=27 by norm_num] using h
    _ = _ := by rw [div_eq_mul_inv]

theorem bounded_log_weight (x R : ℝ) (hx : 0≤x) (hxR : x≤R) :
    1≤(1+R)^3*((1+x)^3)⁻¹ := by
  rw [←div_eq_mul_inv]
  apply (one_le_div (by positivity : 0<(1+x)^3)).2
  exact pow_le_pow_left₀ (by positivity) (by linarith only [hxR]) 3

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortL2Operator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The preliminary L2 realization of the short-time operator. Its
logarithmic kernel norm is used only for continuity and density. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem shortSchwartzToL2_norm (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    ‖shortSchwartzToL2 K hKm hK u hu f‖≤(2*∫ t, ‖K t‖)*‖f.toLp 2 planeMeasure‖ := by
  have he := (shortSlopeOperator_energy K hKm hK u hu f f.continuous.measurable (f.memLp 2 planeMeasure)).2
  have hout := memLp_toL2_norm_sq planeMeasure (shortSlopeOperator K u f) (shortSchwartz_memLp K hKm hK u hu f)
  have hin := memLp_toL2_norm_sq planeMeasure f (f.memLp 2 planeMeasure)
  change ‖shortSchwartzToL2 K hKm hK u hu f‖^2=_ at hout
  change ‖f.toLp 2 planeMeasure‖^2=_ at hin
  rw [←hout,←hin] at he
  have hnonneg : 0≤∫ t, ‖K t‖ := integral_nonneg fun _ => norm_nonneg _
  have hsq : ‖shortSchwartzToL2 K hKm hK u hu f‖^2≤
      ((2*∫ t, ‖K t‖)*‖f.toLp 2 planeMeasure‖)^2 := by
    exact he.trans_eq (by ring)
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) hnonneg) (norm_nonneg _))).1 hsq

theorem shortL2Operator_onSchwartz (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    shortL2Operator K hKm hK u hu (f.toLp 2 planeMeasure)=shortSchwartzToL2 K hKm hK u hu f := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · exact ⟨2*∫ t, ‖K t‖,shortSchwartzToL2_norm K hKm hK u hu⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_ScalarBandDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar basic and reverse-disparity diagonal bounds, without
projecting the test or imposing a spectrum on amplitude slices. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem scalarVector_apply (f : (ℝ×ℝ) → ℂ) (z : ℝ×ℝ) (i : Unit) :
    scalarVector f z i=f z := by
  cases i
  simp only [scalarVector,PiLp.single_apply,ite_true, if_true]

theorem scalarVector_norm (f : (ℝ×ℝ) → ℂ) (z : ℝ×ℝ) : ‖scalarVector f z‖=‖f z‖ := by
  rw [scalarVector,PiLp.norm_single]

theorem scalarVector_measurable (f : (ℝ×ℝ) → ℂ) (hf : Measurable f) :
    Measurable (scalarVector f) := by
  unfold scalarVector PiLp.single
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_iff.mpr
  intro i
  cases i
  simpa only [Pi.single_apply,ite_true, if_true] using hf

theorem scalarBandForm_eq (psi beta : SchwartzMap ℝ ℂ) (N : ℕ) (topLength W center : ℝ)
    (u : (ℝ×ℝ) → ℝ) (f g : (ℝ×ℝ) → ℂ) :
    scalarBandForm psi beta N topLength W center u f g=
      finiteDiagonalBandL1 (N:=N) psi beta topLength W (fun _ : Unit => center) u
        (fun _ => f) (scalarVector g) := by
  simp only [scalarBandForm,finiteDiagonalBandL1,Fintype.sum_unique,scalarVector_apply]

theorem scalar_band_basic (hVariation : LepingleInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ K : ℝ, 0<K ∧ ∀ (N : ℕ) (topLength W w center : ℝ),
      0<topLength → 0<W → 0<w → w≤W → c+B*(w/W)≤w*center → w*center+B*(w/W)≤C →
    ∀ (u : (ℝ×ℝ) → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f g : (ℝ×ℝ) → ℂ), Measurable f → Measurable g →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
      ‖scalarBandForm psi beta N topLength W center u f g‖≤
        K*Real.sqrt (planeMeasure.real F)*Real.sqrt (planeMeasure.real E) := by
  obtain ⟨K,hK,hmain⟩ := band_diagonal_basic_l1 hVariation psi beta B c C a M hB hc hC ha hM hpsi hbeta
  refine ⟨K,hK,?_⟩
  intro N topLength W w center htop hW hw hwW hlo hhi u hum hu f g hfm hgm hfb hgb
    E F hE hF hEfin hFfin hgs hfs
  rw [scalarBandForm_eq]
  exact hmain N Unit topLength W w htop hW hw hwW (fun _ => center) (fun _ => hlo) (fun _ => hhi)
    u hum hu (fun _ => f) (scalarVector f) (scalarVector g)
    (fun z i => (scalarVector_apply f z i).symm) (scalarVector_measurable f hfm) (scalarVector_measurable g hgm)
    (fun z => by rw [scalarVector_norm]; exact hfb z) (fun z => by rw [scalarVector_norm]; exact hgb z)
    E F hE hF hEfin hFfin
    (fun z hz => by simp only [scalarVector,hgs z hz,PiLp.single_eq_zero_iff])
    (fun z hz => by simp only [scalarVector,hfs z hz,PiLp.single_eq_zero_iff])

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ScalarBandKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar annular form is the actual time operator applied to the
original vertical cutoff; the test is not projected. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem annularScalarMultiplier_eq (psi beta : SchwartzMap ℝ ℂ)
    (l W center : ℝ) (hl : 0<l) (u : (ℝ×ℝ) → ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    variableFrequencyMultiplierL1 (annularBandSymbol psi beta l W center u) f z=
      slopeKernelOperator (scaledTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) l) u
        (schwartzVerticalProjection beta W center f) z := by
  rw [schwartz_frozen_slope_multiplier _
    (scaledTimeKernel_integrable (𝓕⁻ psi : SchwartzMap ℝ ℂ) (𝓕⁻ psi : SchwartzMap ℝ ℂ).integrable
      l hl.ne')]
  have hfour (s : ℝ) : 𝓕 (scaledTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) l) s=psi (l*s) := by
    rw [scaledTimeKernel_fourier _ l hl]
    have heq : (𝓕 (𝓕⁻ psi : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ)=psi := fourier_fourierInv_eq psi
    exact congrArg (fun q : SchwartzMap ℝ ℂ => q (l*s)) heq
  unfold variableFrequencyMultiplierL1
  apply integral_congr_ae
  filter_upwards [] with omega
  rw [hfour]
  congr 1
  simp only [annularBandSymbol,symbolY,schwartzVerticalProjection_fourier,mul_assoc]

theorem scalarBandForm_eq_kernel (psi beta : SchwartzMap ℝ ℂ) (N : ℕ)
    (topLength W center : ℝ) (htop : 0<topLength)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u) (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    scalarBandForm psi beta N topLength W center u f g=
      ∫ z, slopeKernelOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength) u
        (schwartzVerticalProjection beta W center f) z*star (g z) ∂planeMeasure := by
  let M := fun j : Fin N => annularBandSymbol psi beta (topLength/(2:ℝ)^j.val) W center u
  have hi (j : Fin N) : Integrable (fun z => variableFrequencyMultiplierL1 (M j) f z*star (g z))
      planeMeasure := by
    apply variableFrequencyMultiplier_pairing_integrable (M j)
      (annularBandSymbol_measurable _ _ _ _ _ u hum)
      (SchwartzMap.seminorm ℝ 0 0 psi*SchwartzMap.seminorm ℝ 0 0 beta) _ f g g.integrable
    intro z omega
    dsimp only [M,annularBandSymbol]
    rw [norm_mul]
    exact mul_le_mul (SchwartzMap.norm_le_seminorm ℝ psi _)
      (SchwartzMap.norm_le_seminorm ℝ beta _) (norm_nonneg _) (apply_nonneg _ _)
  change (∑ j : Fin N, ∫ z, variableFrequencyMultiplierL1 (M j) f z*star (g z) ∂planeMeasure)=_
  rw [←integral_finsetSum _ (fun j _ => hi j)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [slopeKernelOperator_finiteTimeKernel _ N topLength htop,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [annularScalarMultiplier_eq psi beta _ W center (div_pos htop (pow_pos (by norm_num) _))]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ActualScalarBandBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The basic and reverse-disparity estimates for the actual scalar time
operator with the original vertical cutoff and unprojected test. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped ENNReal FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem actual_scalar_band_basic (hVariation : LepingleInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ K : ℝ, 0<K ∧ ∀ (N : ℕ) (topLength W w center : ℝ),
      0<topLength → 0<W → 0<w → w≤W → c+B*(w/W)≤w*center → w*center+B*(w/W)≤C →
    ∀ (u : (ℝ×ℝ) → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
      ‖∫ z, slopeKernelOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength) u
        (schwartzVerticalProjection beta W center f) z*star (g z) ∂planeMeasure‖≤
        K*Real.sqrt (planeMeasure.real F)*Real.sqrt (planeMeasure.real E) := by
  obtain ⟨K,hK,hmain⟩ := scalar_band_basic hVariation psi beta B c C a M hB hc hC ha hM hpsi hbeta
  refine ⟨K,hK,?_⟩
  intro N topLength W w center htop hW hw hwW hlo hhi u hum hu f g hfb hgb
    E F hE hF hEfin hFfin hgs hfs
  rw [←scalarBandForm_eq_kernel psi beta N topLength W center htop u hum f g]
  exact hmain N topLength W w center htop hW hw hwW hlo hhi u hum hu f g
    f.continuous.measurable g.continuous.measurable hfb hgb E F hE hF hEfin hFfin hgs hfs

theorem actual_scalar_band_reverse (hVariation : LepingleInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ K : ℝ, 0<K ∧ ∀ (N : ℕ) (topLength W w center : ℝ),
      0<topLength → 0<W → 0<w → w≤W → c+B*(w/W)≤w*center → w*center+B*(w/W)≤C →
    ∀ (u : (ℝ×ℝ) → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
      ‖∫ z, slopeKernelOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength) u
        (schwartzVerticalProjection beta W center f) z*star (g z) ∂planeMeasure‖≤
        K*Real.sqrt (planeMeasure.real F*planeMeasure.real E)*
          (planeMeasure.real E/planeMeasure.real F)^(9/20:ℝ) := by
  obtain ⟨K,hK,hmain⟩ := scalar_band_reverse hVariation psi beta B c C a M hB hc hC ha hM hpsi hbeta
  refine ⟨K,hK,?_⟩
  intro N topLength W w center htop hW hw hwW hlo hhi u hum hu f g hfb hgb
    E F hE hF hEfin hFfin hgs hfs
  rw [←scalarBandForm_eq_kernel psi beta N topLength W center htop u hum f g]
  exact hmain N topLength W w center htop hW hw hwW hlo hhi u hum hu f g
    f.continuous.measurable g.continuous.measurable hfb hgb E F hE hF hEfin hFfin hgs hfs

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalL2Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual vertical Schwartz multiplier extends to L2. This
preliminary bound supplies continuity for restricted-test approximation. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem verticalSchwartzToL2_norm (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    ‖verticalSchwartzToL2 p w f‖≤verticalProjectionCost p*‖f.toLp 2 planeMeasure‖ := by
  let K := verticalProfileKernel p w 0
  let A := ∫ s, ‖(𝓕⁻ p : SchwartzMap ℝ ℂ) s‖
  have hKm : Measurable K := by
    unfold K verticalProfileKernel modulatedTimeKernel scaledTimeKernel
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (continuous_const.mul ((𝓕⁻ p : SchwartzMap ℝ ℂ).continuous.comp (by fun_prop)))).measurable
  have hKi : Integrable K := modulatedTimeKernel_integrable (𝓕⁻ p) w 0 hw
  have he := (verticalConvolution_energy_bound K hKi hKm f f.continuous.measurable
    (f.memLp 2 planeMeasure)).2
  have hid : verticalConvolution K f=schwartzVerticalProjection p w 0 f := by
    funext z
    exact (schwartzVerticalProjection_eq_convolution p w 0 hw f z).symm
  have hmass : (∫ s, ‖K s‖)=A := modulatedTimeKernel_l1 (𝓕⁻ p) w 0 hw
  rw [hid,hmass] at he
  have hout := memLp_toL2_norm_sq planeMeasure (schwartzVerticalProjection p w 0 f)
    ((schwartzVerticalProjection p w 0 f).memLp 2 planeMeasure)
  have hin := memLp_toL2_norm_sq planeMeasure f (f.memLp 2 planeMeasure)
  change ‖verticalSchwartzToL2 p w f‖^2=_ at hout
  change ‖f.toLp 2 planeMeasure‖^2=_ at hin
  rw [←hout,←hin] at he
  have hA : 0≤A := integral_nonneg fun _ => norm_nonneg _
  have hAC : A≤verticalProjectionCost p := by
    change A≤1+A
    linarith only [hA]
  have hsquare : ‖verticalSchwartzToL2 p w f‖^2≤
      (verticalProjectionCost p*‖f.toLp 2 planeMeasure‖)^2 := by
    apply he.trans
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA hAC 2) (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (verticalProjectionCost_pos p).le (norm_nonneg _))).1 hsquare

theorem verticalL2Projection_onSchwartz (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    verticalL2Projection p w (f.toLp 2 planeMeasure)=(schwartzVerticalProjection p w 0 f).toLp 2 planeMeasure := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · exact ⟨verticalProjectionCost p,verticalSchwartzToL2_norm p w hw⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BandL2Pairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous L2 realization of the actual short-time band pairing. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem bandL2Operator_onSchwartz (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (hw : 0<w) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    bandL2Operator K hKm hK u hu p w (f.toLp 2 planeMeasure)=
      shortSchwartzToL2 K hKm hK u hu (schwartzVerticalProjection p w 0 f) := by
  change shortL2Operator K hKm hK u hu (verticalL2Projection p w (f.toLp 2 planeMeasure))=_
  rw [verticalL2Projection_onSchwartz p w hw,shortL2Operator_onSchwartz]

theorem bandL2Pairing_onSchwartz (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (hw : 0<w) (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    bandL2Pairing K hKm hK u hu p w (f.toLp 2 planeMeasure) (g.toLp 2 planeMeasure)=
      ∫ z, shortSlopeOperator K u (schwartzVerticalProjection p w 0 f) z*star (g z) ∂planeMeasure := by
  change inner ℂ (g.toLp 2 planeMeasure) (bandL2Operator K hKm hK u hu p w (f.toLp 2 planeMeasure))=_
  rw [bandL2Operator_onSchwartz K hKm hK u hu p w hw]
  calc
    _ = ∫ z, inner ℂ (g z) (shortSlopeOperator K u (schwartzVerticalProjection p w 0 f) z) ∂planeMeasure :=
      memLp_inner_integral planeMeasure g (shortSlopeOperator K u (schwartzVerticalProjection p w 0 f))
        (g.memLp 2 planeMeasure) (shortSchwartz_memLp K hKm hK u hu _)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [RCLike.inner_apply, starRingEnd_apply, mul_comm]

theorem bandL2Pairing_kernel (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (hw : 0<w) (f g : SchwartzMap (ℝ×ℝ) ℂ) (l r : ℝ) (hwidth : r-l≤1/4)
    (hf : ∀ z, z.1∉Set.Icc l r → f z=0) (hg : ∀ z, z.1∉Set.Icc l r → g z=0) :
    bandL2Pairing K hKm hK u hu p w (f.toLp 2 planeMeasure) (g.toLp 2 planeMeasure)=
      kernelPairing K u (schwartzVerticalProjection p w 0 f) g := by
  rw [bandL2Pairing_onSchwartz K hKm hK u hu p w hw]
  have hp (z : ℝ×ℝ) (hz : z.1∉Set.Icc l r) : schwartzVerticalProjection p w 0 f z=0 := by
    rw [schwartzVerticalProjection_eq_convolution p w 0 hw]
    exact verticalConvolution_horizontal_support _ f _ hf z hz
  exact integral_congr_ae (Filter.Eventually.of_forall
    (shortSlopeOperator_pairing_eq K u _ g l r hwidth hp hg))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_CenteredBandProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive annular cutoff is exactly a centered cutoff at the same
width, so both scalar endpoint estimates apply to the original input. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped FourierTransform ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem centeredPositiveCutoff_support (p : SchwartzMap ℝ ℂ)
    (hp : ∀ s, p s≠0 → 1 ≤ s ∧ s≤2) :
    ∀ s, centeredPositiveCutoff p s≠0 → |s|≤1/2 := by
  intro s hs
  have h := hp (s+3/2) (by simpa only [centeredPositiveCutoff,
    SchwartzMap.compSubConstCLM_apply,sub_neg_eq_add] using hs)
  exact abs_le.mpr ⟨by linarith [h.1],by linarith [h.2]⟩

theorem centeredPositiveCutoff_projection (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    schwartzVerticalProjection (centeredPositiveCutoff p) w ((3/2)/w) f=
      schwartzVerticalProjection p w 0 f := by
  apply planar_schwartz_ext_fourier
  intro omega
  simp only [schwartzVerticalProjection_fourier,centeredPositiveCutoff,
    SchwartzMap.compSubConstCLM_apply,sub_neg_eq_add,sub_zero]
  congr 2
  field_simp
  ring

theorem actual_positive_band_basic (hVariation : LepingleInput)
    (psi p : SchwartzMap ℝ ℂ) (a M : ℝ) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hp : ∀ s, p s≠0 → 1 ≤ s ∧ s≤2) :
    ∃ K : ℝ, 0<K ∧ ∀ (N : ℕ) (top w : ℝ), 0<top → 0<w →
    ∀ (u : (ℝ×ℝ) → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
      ‖∫ z, slopeKernelOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N top) u
        (schwartzVerticalProjection p w 0 f) z*star (g z) ∂planeMeasure‖≤
        K*Real.sqrt (planeMeasure.real F)*Real.sqrt (planeMeasure.real E) := by
  obtain ⟨K,hK,hbound⟩ := actual_scalar_band_basic hVariation psi (centeredPositiveCutoff p)
    1 (1/2) (5/2) a M (by norm_num) (by norm_num) (by norm_num) ha hM hpsi
    (centeredPositiveCutoff_support p hp)
  refine ⟨K,hK,?_⟩
  intro N top w htop hw u hum hub f g hf hg E F hE hF hEfin hFfin hgs hfs
  have hcenter : w*((3/2)/w)=3/2 := mul_div_cancel₀ _ hw.ne'
  have h := hbound N top w w ((3/2)/w) htop hw hw le_rfl
    (by rw [div_self hw.ne',hcenter]; norm_num)
    (by rw [div_self hw.ne',hcenter]; norm_num)
    u hum hub f g hf hg E F hE hF hEfin hFfin hgs hfs
  rwa [centeredPositiveCutoff_projection p w hw] at h

theorem actual_positive_band_reverse (hVariation : LepingleInput)
    (psi p : SchwartzMap ℝ ℂ) (a M : ℝ) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hp : ∀ s, p s≠0 → 1 ≤ s ∧ s≤2) :
    ∃ K : ℝ, 0<K ∧ ∀ (N : ℕ) (top w : ℝ), 0<top → 0<w →
    ∀ (u : (ℝ×ℝ) → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
      ‖∫ z, slopeKernelOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N top) u
        (schwartzVerticalProjection p w 0 f) z*star (g z) ∂planeMeasure‖≤
        K*Real.sqrt (planeMeasure.real F*planeMeasure.real E)*
          (planeMeasure.real E/planeMeasure.real F)^(9/20:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := actual_scalar_band_reverse hVariation psi (centeredPositiveCutoff p)
    1 (1/2) (5/2) a M (by norm_num) (by norm_num) (by norm_num) ha hM hpsi
    (centeredPositiveCutoff_support p hp)
  refine ⟨K,hK,?_⟩
  intro N top w htop hw u hum hub f g hf hg E F hE hF hEfin hFfin hgs hfs
  have hcenter : w*((3/2)/w)=3/2 := mul_div_cancel₀ _ hw.ne'
  have h := hbound N top w w ((3/2)/w) htop hw hw le_rfl
    (by rw [div_self hw.ne',hcenter]; norm_num)
    (by rw [div_self hw.ne',hcenter]; norm_num)
    u hum hub f g hf hg E F hE hF hEfin hFfin hgs hfs
  rwa [centeredPositiveCutoff_projection p w hw] at h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_RestrictedSchwartzSizes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual integral sizes of restricted Schwartz tests and the elementary
mass inequalities used to combine the scalar endpoint remainders. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem restrictedSchwartz_l1 (f : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1)
    (A : Set (ℝ×ℝ)) (hA : MeasurableSet A) (hAfin : planeMeasure A≠∞)
    (hsupp : ∀ z, z∉A → f z=0) :
    (∫ z, ‖f z‖ ∂planeMeasure)≤planeMeasure.real A := by
  have hi : Integrable (A.indicator (fun _ : ℝ×ℝ => (1:ℝ))) planeMeasure :=
    (integrableOn_const hAfin).integrable_indicator hA
  calc
    _ ≤ ∫ z, A.indicator (fun _ : ℝ×ℝ => (1:ℝ)) z ∂planeMeasure := by
      apply integral_mono f.integrable.norm hi
      intro z
      by_cases hz : z∈A
      · simpa only [Set.indicator_of_mem hz] using hf z
      · simp only [Set.indicator_of_notMem hz,hsupp z hz,norm_zero,le_refl]
    _ = _ := by simpa only [smul_eq_mul,mul_one] using integral_indicator_const (1:ℝ) hA

theorem restrictedSchwartz_energy (f : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1)
    (A : Set (ℝ×ℝ)) (hA : MeasurableSet A) (hAfin : planeMeasure A≠∞)
    (hsupp : ∀ z, z∉A → f z=0) :
    (∫ z, ‖f z‖^2 ∂planeMeasure)≤planeMeasure.real A := by
  have h := schwartz_power_le_l1 f hf 2 (by norm_num)
  rw [show (fun z : ℝ×ℝ => ‖f z‖^(2:ℝ))=(fun z => ‖f z‖^2) by
    funext z; exact Real.rpow_two _] at h
  exact h.trans (restrictedSchwartz_l1 f hf A hA hAfin hsupp)

theorem min_mass_le_sqrt (F E : ℝ) (hF : 0≤F) (hE : 0≤E) :
    min (4*F) E≤4*(Real.sqrt F*Real.sqrt E) := by
  have hmin : min F E≤Real.sqrt F*Real.sqrt E := by
    rcases le_total F E with h | h
    · rw [min_eq_left h]
      calc
        F = Real.sqrt F*Real.sqrt F := (Real.mul_self_sqrt hF).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg _)
    · rw [min_eq_right h]
      calc
        E = Real.sqrt E*Real.sqrt E := (Real.mul_self_sqrt hE).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg _)
  calc
    min (4*F) E ≤ min (4*F) (4*E) := min_le_min le_rfl (by linarith)
    _ = 4*min F E := (mul_min_of_nonneg F E (by norm_num)).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hmin (by norm_num)

theorem reverse_mass_bound (F E : ℝ) (hF : 0<F) (hE : 0<E) (hEF : E≤F) :
    E≤Real.sqrt (F*E)*(E/F)^(9/20:ℝ) := by
  let r := E/F
  have hr : 0 < r := div_pos hE hF
  have hr1 : r≤1 := (div_le_one hF).2 hEF
  have heq : E=F*r := by dsimp [r]; field_simp
  have hs : Real.sqrt (F*E)=F*Real.sqrt r := by
    rw [heq,←mul_assoc,←pow_two,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hF]
  change E≤Real.sqrt (F*E)*r^(9/20:ℝ)
  rw [hs,Real.sqrt_eq_rpow,heq,mul_assoc,←Real.rpow_add hr]
  apply mul_le_mul_of_nonneg_left _ hF.le
  exact Real.self_le_rpow_of_le_one hr.le hr1 (by norm_num)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SharpBandScalarEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar basic and reverse-disparity estimates pass to every
actual sharp truncation, on the original restricted Schwartz inputs. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem actual_sharp_band_basic (hVariation : LepingleInput) (p : SchwartzMap ℝ ℂ)
    (hp : ∀ s, p s≠0 → 1 ≤ s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, 0<epsilon → epsilon≤R → 0<w →
    ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u → (∀ z, |u z|≤1) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
    ∀ l r : ℝ, r-l≤1/4 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel epsilon R) u (schwartzVerticalProjection p w 0 f) g‖≤
        C*Real.sqrt (planeMeasure.real F)*Real.sqrt (planeMeasure.real E) := by
  obtain ⟨K,hK,hmain⟩ := actual_positive_band_basic hVariation hilbertAnnularSymbol p (1/2) 2
    (by norm_num) (by norm_num) hilbertAnnularSymbol_support hp
  obtain ⟨B,hB,herror⟩ := hilbertProjected_middle_error
  have hP := verticalProjectionCost_pos p
  refine ⟨K+4*(verticalProjectionCost p*B),by positivity,?_⟩
  intro epsilon R w he heR hw u hu hub f g hf hg E F hE hF hEfin hFfin hgs hfs l r hwidth hfstrip hgstrip
  have hR : 0<R := he.trans_le heR
  obtain ⟨N,_,_,herr⟩ := herror epsilon R he heR
  have he1 := restrictedSchwartz_l1 g hg E hE hEfin hgs
  have hf1 := restrictedSchwartz_l1 f hf F hF hFfin hfs
  have hb := herr u hu p w hw f g hf hg l r hwidth hfstrip hgstrip
  have hmass : min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)≤
      4*(Real.sqrt (planeMeasure.real F)*Real.sqrt (planeMeasure.real E)) :=
    (min_le_min (mul_le_mul_of_nonneg_left hf1 (by norm_num)) he1).trans
      (min_mass_le_sqrt _ _ measureReal_nonneg measureReal_nonneg)
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hmass (mul_nonneg hP.le hB))
  have hm := hmain N (R/2) w (by positivity) hw u hu.continuous.measurable hub
    f g hf hg E F hE hF hEfin hFfin hgs hfs
  exact (norm_le_insert' _ _).trans ((add_le_add hm hb').trans_eq (by ring))

theorem actual_sharp_band_reverse (hVariation : LepingleInput) (p : SchwartzMap ℝ ℂ)
    (hp : ∀ s, p s≠0 → 1 ≤ s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, 0<epsilon → epsilon≤R → 0<w →
    ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u → (∀ z, |u z|≤1) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      0<planeMeasure.real F → 0<planeMeasure.real E → planeMeasure.real E≤planeMeasure.real F →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
    ∀ l r : ℝ, r-l≤1/4 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel epsilon R) u (schwartzVerticalProjection p w 0 f) g‖≤
        C*Real.sqrt (planeMeasure.real F*planeMeasure.real E)*
          (planeMeasure.real E/planeMeasure.real F)^(9/20:ℝ) := by
  obtain ⟨K,hK,hmain⟩ := actual_positive_band_reverse hVariation hilbertAnnularSymbol p (1/2) 2
    (by norm_num) (by norm_num) hilbertAnnularSymbol_support hp
  obtain ⟨B,hB,herror⟩ := hilbertProjected_middle_error
  have hP := verticalProjectionCost_pos p
  refine ⟨K+verticalProjectionCost p*B,by positivity,?_⟩
  intro epsilon R w he heR hw u hu hub f g hf hg E F hE hF hEfin hFfin hFpos hEpos hEF hgs hfs
    l r hwidth hfstrip hgstrip
  have hR : 0<R := he.trans_le heR
  obtain ⟨N,_,_,herr⟩ := herror epsilon R he heR
  have he1 := restrictedSchwartz_l1 g hg E hE hEfin hgs
  have hb := herr u hu p w hw f g hf hg l r hwidth hfstrip hgstrip
  have hmass : min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)≤
      Real.sqrt (planeMeasure.real F*planeMeasure.real E)*
        (planeMeasure.real E/planeMeasure.real F)^(9/20:ℝ) :=
    ((min_le_right _ _).trans he1).trans (reverse_mass_bound _ _ hFpos hEpos hEF)
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hmass (mul_nonneg hP.le hB))
  have hm := hmain N (R/2) w (by positivity) hw u hu.continuous.measurable hub
    f g hf hg E F hE hF hEfin hFfin hgs hfs
  exact (norm_le_insert' _ _).trans ((add_le_add hm hb').trans_eq (by ring))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SharpBandRestrictedLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three actual sharp band regimes give the logarithmic restricted
estimate on Schwartz tests, uniformly in the inner endpoint and width. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem log_mass_ratio (F E ratio : ℝ) (hF : 0<F) (hr : 0 < ratio)
    (heq : E=ratio^2*F) : Real.log (F/E)= -2*Real.log ratio := by
  have hE : 0<E := heq ▸ mul_pos (pow_pos hr 2) hF
  rw [Real.log_div hF.ne' hE.ne',heq,Real.log_mul (pow_pos hr 2).ne' hF.ne',Real.log_pow]
  ring

theorem actual_sharp_band_restricted_log (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ)
    (hp : ∀ s, p s≠0 → 1 ≤ s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, 0<epsilon → epsilon≤R → R≤1/4 → 0<w →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      0<planeMeasure.real F → 0<planeMeasure.real E →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
    ∀ l r : ℝ, 600*(r-l)≤1 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel epsilon R) (fun z => field (planeCoordinates z))
        (schwartzVerticalProjection p w 0 f) g‖≤
        C*((1+|Real.log (planeMeasure.real F/planeMeasure.real E)|)^3)⁻¹*
          Real.sqrt (planeMeasure.real F)*Real.sqrt (planeMeasure.real E) := by
  obtain ⟨Cb,hCb,hbasic⟩ := actual_sharp_band_basic hVariation p hp
  obtain ⟨Cr,hCr,hreverse⟩ := actual_sharp_band_reverse hVariation p hp
  obtain ⟨Ch,L0,hCh,hL0,hhigh⟩ := actual_sharp_band_uniform_high hVariation hLL hH p hp
  obtain ⟨D,hD,hexp⟩ := exponential_log_weight (9/20) (by norm_num)
  let C := Cb*(1+2*L0)^3+Cr*D+27*Ch
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro epsilon R w he heR hRquarter hw field hfield hfieldBound f g hf hg E F hE hF hEfin hFfin
    hFpos hEpos hgs hfs l r hstrip hfstrip hgstrip
  let a := planeMeasure.real F
  let b := planeMeasure.real E
  let weight := ((1+|Real.log (a/b)|)^3)⁻¹
  let root := Real.sqrt a*Real.sqrt b
  let u := fun z : ℝ×ℝ => field (planeCoordinates z)
  let value := kernelPairing (sharpTimeKernel epsilon R) u (schwartzVerticalProjection p w 0 f) g
  have ha : 0<a := hFpos
  have hb : 0<b := hEpos
  have hwgt : 0≤weight := by dsimp [weight]; positivity
  have hroot : 0 ≤ root := by dsimp [root]; positivity
  have hu : LipschitzWith 2 u := by simpa only [u,mul_one] using product_slope_lipschitz field hfield
  have hub (z) : |u z|≤1 := (hfieldBound _).trans (by norm_num)
  have hwidth : r-l≤1/4 := by linarith only [hstrip]
  have hbpos : 0≤Cb*(1+2*L0)^3 := by positivity
  have hrpos : 0≤Cr*D := by positivity
  have hhpos : 0≤27*Ch := by positivity
  have hCbC : Cb*(1+2*L0)^3≤C := by dsimp [C]; linarith only [hrpos,hhpos]
  have hCrC : Cr*D≤C := by dsimp [C]; linarith only [hbpos,hhpos]
  have hChC : 27*Ch≤C := by dsimp [C]; linarith only [hbpos,hrpos]
  change ‖value‖≤C*weight*Real.sqrt a*Real.sqrt b
  rw [mul_assoc (C*weight)]
  change ‖value‖≤C*weight*root
  by_cases hba : b≤a
  · have hbound := hreverse epsilon R w he heR hw u hu hub f g hf hg E F hE hF hEfin hFfin
      hFpos hEpos hba hgs hfs l r hwidth hfstrip hgstrip
    let x := Real.log (a/b)
    have hx : 0≤x := Real.log_nonneg ((one_le_div hb).2 hba)
    have hpow : (b/a)^(9/20:ℝ)=Real.exp (-(9/20:ℝ)*x) := by
      rw [Real.rpow_def_of_pos (div_pos hb ha)]
      congr 1
      dsimp [x]
      rw [Real.log_div hb.ne' ha.ne',Real.log_div ha.ne' hb.ne']
      ring
    have hxweight : ((1+x)^3)⁻¹=weight := by
      dsimp only [weight,x]
      rw [abs_of_nonneg hx]
    have hdecay := hexp x hx
    rw [hxweight] at hdecay
    calc
      ‖value‖ ≤ Cr*root*Real.exp (-(9/20:ℝ)*x) := by
        simpa only [a,b,root,Real.sqrt_mul ha.le,hpow] using hbound
      _ ≤ Cr*root*(D*weight) := mul_le_mul_of_nonneg_left hdecay (mul_nonneg hCr.le hroot)
      _ = (Cr*D)*weight*root := by ring
      _ ≤ C*weight*root := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCrC hwgt) hroot
  · let ratio := Real.sqrt (b/a)
    obtain ⟨hr,heq⟩ := sqrt_mass_ratio a b ha hb
    let L := Real.log ratio
    have hlog : Real.log (a/b)= -2*L := log_mass_ratio a b ratio ha hr heq
    have hab : a≤b := (lt_of_not_ge hba).le
    have hlognonpos : Real.log (a/b)≤0 := Real.log_nonpos (div_pos ha hb).le ((div_le_one hb).2 hab)
    have hL : 0≤L := by linarith only [hlog,hlognonpos]
    have habs : |Real.log (a/b)|=2*L := by rw [abs_of_nonpos hlognonpos,hlog]; ring
    by_cases hLL0 : L0≤L
    · have hbound := hhigh L hLL0 epsilon R w he heR hRquarter hw field hfield hfieldBound f g
        a b ratio ha hb hr heq rfl hf hg
        (restrictedSchwartz_l1 f hf F hF hFfin hfs) (restrictedSchwartz_l1 g hg E hE hEfin hgs)
        (restrictedSchwartz_energy f hf F hF hFfin hfs) (restrictedSchwartz_energy g hg E hE hEfin hgs)
        l r hstrip hfstrip hgstrip
      have hweight := high_log_weight L (by linarith only [hL0,hLL0])
      have hwid : ((1+2*L)^3)⁻¹=weight := by dsimp only [weight]; rw [habs]
      rw [hwid] at hweight
      calc
        ‖value‖ ≤ Ch*L^(-19:ℝ)*root := by simpa only [mul_assoc,root] using hbound
        _ ≤ Ch*(27*weight)*root := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hweight hCh.le) hroot
        _ = (27*Ch)*weight*root := by ring
        _ ≤ C*weight*root := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hChC hwgt) hroot
    · have hbound := hbasic epsilon R w he heR hw u hu hub f g hf hg E F hE hF hEfin hFfin hgs hfs
        l r hwidth hfstrip hgstrip
      have hweight : 1≤(1+2*L0)^3*weight := by
        have h := bounded_log_weight (2*L) (2*L0) (by positivity) (by linarith only [hLL0])
        simpa only [weight,habs] using h
      calc
        ‖value‖ ≤ Cb*root := by simpa only [a,b,root,mul_assoc] using hbound
        _ ≤ Cb*root*((1+2*L0)^3*weight) :=
          le_mul_of_one_le_right (mul_nonneg hCb.le hroot) hweight
        _ = (Cb*(1+2*L0)^3)*weight*root := by ring
        _ ≤ C*weight*root := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCbC hwgt) hroot

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SharpBandMeasurableRestricted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual sharp band logarithmic estimate for bounded measurable
L2 tests. The slight strip margin is used only for smooth approximation. -/
noncomputable section
open Set MeasureTheory Function
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem support_into_open_strip (f : (ℝ×ℝ) → ℂ) (l r : ℝ)
    (hf : ∀ z, z.1∉Icc l r → f z=0) :
    support f⊆{z : ℝ×ℝ | z.1∈Ioo (l-1/2400) (r+1/2400)} := by
  intro z hz
  have hi : z.1∈Icc l r := by
    by_contra hn
    exact hz (hf z hn)
  constructor <;> linarith only [hi.1,hi.2]

theorem schwartz_open_strip_zero (f : SchwartzMap (ℝ×ℝ) ℂ) (l r : ℝ)
    (hf : support f⊆{z : ℝ×ℝ | z.1∈Ioo l r}) :
    ∀ z, z.1∉Icc l r → f z=0 := by
  intro z hz
  apply notMem_support.mp
  intro hs
  exact hz (Ioo_subset_Icc_self (hf hs))

theorem actual_sharp_band_measurable_restricted_log_oai
    (hVariation : LepingleInput) (hLL : LaceyLiInput) (hH : HorizontalHilbertInput)
    (p : SchwartzMap ℝ ℂ) (hp : ∀ s, p s≠0 → 1 ≤ s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) → R≤1/4 → 0<w →
    ∀ (field : Plane → ℝ) (hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
    ∀ (f g : (ℝ×ℝ) → ℂ), Measurable f → Measurable g →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      0<planeMeasure.real F → 0<planeMeasure.real E → support f⊆F → support g⊆E →
    ∀ l r : ℝ, 1200*(r-l)≤1 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
    ∀ (hf2 : MemLp f 2 planeMeasure) (hg2 : MemLp g 2 planeMeasure),
      ‖sharpBandL2Pairing epsilon R he (he.trans_le heR) field hfield p w (hf2.toLp f) (hg2.toLp g)‖≤
        restrictedLogFactor C (planeMeasure.real F) (planeMeasure.real E) := by
  obtain ⟨C,hC,hbound⟩ := actual_sharp_band_restricted_log hVariation hLL hH p hp
  refine ⟨C,hC,?_⟩
  intro epsilon R w he heR hR hw field hfield hfb f g hfm hgm hf hg E F hE hF hEfin hFfin
    hFpos hEpos hfs hgs l r hwidth hfstrip hgstrip hf2 hg2
  let V := {z : ℝ×ℝ | z.1∈Ioo (l-1/2400) (r+1/2400)}
  have hV : IsOpen V := isOpen_Ioo.preimage continuous_fst
  have hwide : 600*((r+1/2400)-(l-1/2400))≤1 := by linarith only [hwidth]
  apply restricted_log_density _ C V hV _ f g hfm hgm hf hg
    (support_into_open_strip f l r hfstrip) (support_into_open_strip g l r hgstrip)
    F E hF hE hFfin hEfin hFpos hEpos hfs hgs hf2 hg2
  intro fn gn hfnb hgnb hfnV hgnV Fn Gn hFn hGn hFnfin hGnfin hFnpos hGnpos hfns hgns
  have hfnstrip := schwartz_open_strip_zero fn (l-1/2400) (r+1/2400) hfnV
  have hgnstrip := schwartz_open_strip_zero gn (l-1/2400) (r+1/2400) hgnV
  have hb := hbound epsilon R w he heR hR hw field hfield hfb fn gn hfnb hgnb Gn Fn
    hGn hFn hGnfin hFnfin hFnpos hGnpos
    (fun z hz => notMem_support.mp (fun hs => hz (hgns hs)))
    (fun z hz => notMem_support.mp (fun hs => hz (hfns hs)))
    (l-1/2400) (r+1/2400) hwide hfnstrip hgnstrip
  change ‖bandL2Pairing _ _ _ _ _ p w _ _‖≤_
  rw [bandL2Pairing_kernel _ _ _ _ _ p w hw fn gn (l-1/2400) (r+1/2400)
    (by linarith only [hwide]) hfnstrip hgnstrip]
  exact hb

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_measurable_restricted_log_oai := @OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_measurable_restricted_log_oai
