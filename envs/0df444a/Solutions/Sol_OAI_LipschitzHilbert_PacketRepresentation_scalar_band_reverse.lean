-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketRepresentation.scalar_band_reverse
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:28:14.780799+00:00
-- url     : https://prove2.me/submissions/ddcfd5bc-9deb-4fdb-9259-f1f37b015d14

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_exists_angular_reverse_pairing

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

theorem annularCutoff_one (a b : ℝ) (ha : 0<a) (hb : 0<b) (U : ℝ)
    (hlo : a≤|U|) (hhi : |U|≤b) : annularCutoff a b ha hb U=1 := by
  have hi : selectorInner a ha U=0 :=
    (selectorInner a ha).zero_of_le_dist (by simpa [selectorInner, Real.dist_eq] using hlo)
  have ho : selectorOuter b hb U=1 :=
    (selectorOuter b hb).one_of_mem_closedBall (by simpa [selectorOuter, Real.dist_eq] using hhi)
  rw [annularCutoff_apply, hi, ho]
  norm_num

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedReverseConvolution
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reverse disparity for the actual normalized finite convolution sum,
with the constructed angular models and common lattice average. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_normalized_reverse_convolution (hVariation : LepingleInput)
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
        K*Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
          ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ) := by
  obtain ⟨CD,CS,CT,CZ,_hCD,_hCS,_hCT,_hCZ,hreverse⟩ := PacketLatticeData.exists_angular_reverse_pairing
    hVariation (2*Real.pi*A) cEta CEta cb (2*Real.pi*B) radius M
    (by positivity) hcEta hCEta (by positivity) hcb hcbQuarter hsmall hr hcoverSmall num
  let budget : ℝ := ((2:ℝ)^order*C)*3^(2*order)
  let bound : ℝ := max 1 budget
  have hbound_one : 1≤bound := le_max_left _ _
  have hbudget : budget≤bound := le_max_right _ _
  let cost := num.reverseUnitCost M CD CS CT CZ*(2*bound)^4
  let K := 3*max 1 cost
  have hK : 0<K := mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  refine ⟨K,hK,?_⟩
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
    (K*Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
      ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ))
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
  have hresult := hreverse N κ Label (fun j l => finiteSiteFiber labels S j l) P Finset.univ w F
    hw hW hF horder hfreq hlocal
    (fun j l a k xi et hs => (hspec j l a k xi et hs).1)
    (fun j l a k xi et hs => (hspec j l a k xi et hs).2) alt hAlt
    (fun j l a k xi et hs => (haspec j l a k xi et hs).1)
    (fun j l a k xi et hs => (haspec j l a k xi et hs).2)
    b hb hb1 haway hradius hnear bound hbound_one
    (by change budget≤bound; exact hbudget)
    g f hgm hfm hgb hfb E Fset hE hFset hEfin hFfin hgs hfs u hu
  calc
    _ ≤ 3*(cost*Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
        ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ)) := hresult.2
    _ = (3*cost)*(Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
        ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ)) := by ring
    _ ≤ K*(Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
        ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (le_max_right 1 cost) (by norm_num)
    _ = _ := by ring

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedSymbolReverseL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reverse-disparity model estimate for the original finite normalized symbol
form, using the actual annular selectors and the common Fourier average. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_normalized_symbol_reverse_l1 (hVariation : LepingleInput)
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
        K*Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
          ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ) := by
  obtain ⟨Kb,hKb,hreverse⟩ := exists_normalized_reverse_convolution hVariation
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
        Kb*Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
          ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ) := by
    apply hreverse N κ Label chiA chiB q nu hchiA hchiB (hprofiles nu).1 (hprofiles nu).2
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
    (Kb*Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
          ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ)) hconv
  apply hout.trans
  have hbnd : (∫ nu : SymbolSpace, symbolWeight q nu)≤(∫ nu : SymbolSpace, symbolWeight q nu)+1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hbnd
    (show 0 ≤ selectorNormalizer chi Csymbol*Kb*Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
          ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ) by positivity)
  dsimp only [K]
  first | (convert hmul using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hmul.trans (le_of_eq (by ring)))

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PartitionedAnnularReverseL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite partitioned annular multiplier has a uniform reverse-disparity bound.
The fixed symbol and profile costs are constructed, not assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_partitioned_annular_reverse_l1 (hVariation : LepingleInput)
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
        K*Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
          ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ) := by
  obtain ⟨q,hq,Cprofile,_Lp,hCp,_hLp,hprofiles,_hbudget⟩ :=
    exists_normalized_profile_budget (planarInverseSchwartz chiA) (planarInverseSchwartz chiB) 0
  obtain ⟨Csymbol,hCs,hS⟩ := partitionedSymbol_uniform psi (dilatedSlopeWindow rho p.H p.H_pos.ne') beta
    (p.H*c) (mul_pos p.H_pos p.hc) p.R p.hR q
  obtain ⟨K,hK,hreverse⟩ := exists_normalized_symbol_reverse_l1 hVariation chiA chiB q hq
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
  exact hreverse N κ Label topLength width (p.H*w) F htop hwidth (mul_pos p.H_pos hw) hW hF
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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_FiniteDiagonalReverseL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform reverse-disparity estimate for the actual finite diagonal band form.
Slope labels, plateaus, compact symbols, and profile budgets are all
constructed inside the proof. The scalar width W=w is included. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_finite_diagonal_reverse_l1 (hVariation : LepingleInput)
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
        K*Real.sqrt (planeMeasure.real Fset*planeMeasure.real E)*
          (planeMeasure.real E/planeMeasure.real Fset)^(9/20:ℝ) := by
  let p' := p.enlargeVertical
  let beta' := verticallyRescaledWindow beta p.H p.H_pos
  let chi := rectangularFrequencyCutoff A (p.H*B) hA (mul_pos p.H_pos hB)
  obtain ⟨multiplicity,hmult⟩ := exists_finiteSlopeCenter_multiplicity delta p.H hd p.H_pos.le
  obtain ⟨K,hK,hmain⟩ := exists_partitioned_annular_reverse_l1 hVariation psi
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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_BandDiagonalReverseL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reverse-disparity diagonal estimate with only the original annular support
and bin hypotheses. All packet geometry is constructed internally. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem band_diagonal_reverse_l1 (hVariation : LepingleInput)
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
        K*Real.sqrt (planeMeasure.real Fset*planeMeasure.real E)*
          (planeMeasure.real E/planeMeasure.real Fset)^(9/20:ℝ) := by
  obtain ⟨A,delta,p,hA,hd,hnarrow⟩ := exists_diagonal_geometry B c C a M hB hc hC ha hM
  obtain ⟨K,hK,hmain⟩ := exists_finite_diagonal_reverse_l1 hVariation psi beta A B c C a M delta
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

theorem scalar_band_reverse_oai (hVariation : LepingleInput)
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
        K*Real.sqrt (planeMeasure.real F*planeMeasure.real E)*
          (planeMeasure.real E/planeMeasure.real F)^(9/20:ℝ) := by
  obtain ⟨K,hK,hmain⟩ := band_diagonal_reverse_l1 hVariation psi beta B c C a M hB hc hC ha hM hpsi hbeta
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

theorem solution : type_of% @OAI.LipschitzHilbert.PacketRepresentation.scalar_band_reverse_oai := @OAI.LipschitzHilbert.PacketRepresentation.scalar_band_reverse_oai
