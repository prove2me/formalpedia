-- Prove2me | solution 1 for OAI.Erdos3.adaptiveAffineSideLog_reference_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T17:48:23.251924+00:00
-- url     : https://prove2.me/submissions/508244c7-3b8f-4abb-a20b-c1295eee78b1

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090
import Theorems.Thm_OAI_Erdos3_affineCommonReferenceBudget_bounds
import Theorems.Thm_OAI_Erdos3_affineComparisonMoment_bounds
import Theorems.Thm_OAI_Erdos3_affineComparisonScale_bounds

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SpectralLogBudget
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3

theorem log_sixteen_div_le {epsilon A : ℝ} (hepsilon : 0 < epsilon)
    (hinverse : epsilon⁻¹ ≤ Real.exp A) : Real.log (16 / epsilon) ≤ A + 4 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    calc
      16 = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) htwo 4
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hb : 16 / epsilon ≤ Real.exp (A + 4) := by
    calc
      _ = 16 * epsilon⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp 4 * Real.exp A :=
        mul_le_mul h16 hinverse (inv_nonneg.mpr hepsilon.le) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 16 / epsilon) hb
  simpa only [Real.log_exp] using hlog

theorem CyclicCrootSisask.spectralIterations_le_logBudget {epsilon p A : ℝ}
    (hepsilon : 0 < epsilon) (hp : 0 ≤ p) (hA : 0 ≤ A)
    (hinverse : epsilon⁻¹ ≤ Real.exp A) :
    (spectralIterations epsilon p : ℝ) ≤ 2 * (p + A + 4) + 2 := by
  have hlog := log_sixteen_div_le hepsilon hinverse
  have hhalf : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : (p + Real.log (16 / epsilon)) / Real.log 2 ≤ 2 * (p + A + 4) := by
    apply (div_le_iff₀ htwo).mpr
    have hm := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ 2 * (p + A + 4))
    nlinarith
  have hm : (⌈(p + Real.log (16 / epsilon)) / Real.log 2⌉₊ : ℝ) ≤
      (⌈2 * (p + A + 4)⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_mono hdiv
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * (p + A + 4))
  unfold spectralIterations
  push_cast
  linarith

theorem affineAllowance_inverse_le_exp {epsilon A : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hinverse : epsilon⁻¹ ≤ Real.exp A) :
    (epsilon / (2 + epsilon))⁻¹ ≤ Real.exp (A + 2) := by
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  rw [inv_div, div_eq_mul_inv]
  calc
    _ ≤ 3 * Real.exp A := mul_le_mul (by linarith) hinverse
      (inv_nonneg.mpr hepsilon.le) (by norm_num)
    _ ≤ Real.exp 2 * Real.exp A := mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffinePrimitiveLogBudget
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem affinePrimitiveLogBudget_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ affinePrimitiveLogBudget P := by unfold affinePrimitiveLogBudget; positivity

theorem affineRemovalDepth_le_logBudget {T P : ℝ} (hT : 0 ≤ T) (hTP : T ≤ P) :
    (affineRemovalDepth T : ℝ) ≤ 2 * P + 10 := by
  have h := CyclicCrootSisask.spectralIterations_le_logBudget (epsilon := 1) (A := 0)
    (by norm_num) hT le_rfl (by simp)
  change (affineRemovalDepth T : ℝ) ≤ _ at h
  linarith

theorem affineComparisonTail_le_logBudget {epsilon L T P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hLP : L ≤ P) (hTP : T ≤ P)
    (hinverse : epsilon⁻¹ ≤ Real.exp P) :
    (affineComparisonTail epsilon L T : ℝ) ≤ 8 * P + 22 := by
  have h := CyclicCrootSisask.spectralIterations_le_logBudget
    (epsilon := epsilon / (2 + epsilon)) (p := L + 2 * T + 4) (A := P + 2)
    (by positivity) (by positivity) (by positivity)
    (affineAllowance_inverse_le_exp hepsilon hepsilon1 hinverse)
  change (affineComparisonTail epsilon L T : ℝ) ≤ _ at h
  linarith

theorem affineComparisonPrimitive_bounds {epsilon L T C P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hLP : L ≤ P) (hTP : T ≤ P) (hCP : C ≤ P)
    (hinverse : epsilon⁻¹ ≤ Real.exp P) :
    ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤ affinePrimitiveLogBudget P ∧
      affineComparisonScale epsilon L T C ≤ affinePrimitiveLogBudget P ∧
      (affineComparisonMoment (affineComparisonScale epsilon L T C) : ℝ) ≤ affinePrimitiveLogBudget P + 2 := by
  have hj := affineRemovalDepth_le_logBudget hT hTP
  have ht := affineComparisonTail_le_logBudget hepsilon hepsilon1 hP hL hT hLP hTP hinverse
  have hsum : ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤
      10 * P + 32 := by push_cast; linarith
  have hs : affineComparisonScale epsilon L T C ≤ affinePrimitiveLogBudget P := by
    unfold affineComparisonScale affinePrimitiveLogBudget
    linarith
  refine ⟨?_, hs, ?_⟩
  · unfold affinePrimitiveLogBudget
    linarith
  · have hm := (affineComparisonMoment_bounds (affineComparisonScale_bounds (ε := epsilon) hL hT hC).1).2.2.2
    linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeFamilyCutoff
namespace OAI

section

namespace Erdos3

theorem adaptiveAffineShell_pos (A sourceDim siteDim : ℕ)
    (ε L T C modLog : ℝ) {totalShell : ℝ} (h : 0 < totalShell) :
    0 < adaptiveAffineShell A sourceDim siteDim ε L T C totalShell modLog :=
  mul_pos h (Real.exp_pos _)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AdaptiveShellLogBudget
namespace OAI

section

namespace Erdos3

theorem affineShellLogBudget_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ affineCountLogBudget P ∧ 0 ≤ affineShellLogBudget P := by
  have hH := affinePrimitiveLogBudget_nonneg hP
  have hc : 0 ≤ affineCountLogBudget P := by unfold affineCountLogBudget; positivity
  exact ⟨hc, add_nonneg hP hc⟩

theorem adaptiveAffineCountLog_le_budget (A sourceDim siteDim : ℕ)
    {epsilon L T C modLog P : ℝ} (hP : 0 ≤ P) (hmod0 : 0 ≤ modLog)
    (hA : (A : ℝ) ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hmod : modLog ≤ P) (hscale0 : 0 ≤ affineComparisonScale epsilon L T C)
    (hscale : affineComparisonScale epsilon L T C ≤ affinePrimitiveLogBudget P) :
    adaptiveAffineCountLog A sourceDim siteDim epsilon L T C modLog ≤ affineCountLogBudget P := by
  have hs := mul_le_mul hsource hmod hmod0 hP
  have ht := mul_le_mul hsite hmod hmod0 hP
  have hi : affineComparisonScale epsilon L T C + (sourceDim : ℝ) * modLog +
      (siteDim : ℝ) * modLog + 1 ≤ affinePrimitiveLogBudget P + 2 * P ^ 2 + 1 := by nlinarith
  unfold adaptiveAffineCountLog affineCountLogBudget
  exact mul_le_mul hA hi (by positivity) hP

theorem adaptiveAffineShell_inverse_le_budget (A sourceDim siteDim : ℕ)
    {epsilon L T C modLog totalShell P : ℝ}
    (htotal : 0 < totalShell) (htotalInv : totalShell⁻¹ ≤ Real.exp P)
    (hcount : adaptiveAffineCountLog A sourceDim siteDim epsilon L T C modLog ≤ affineCountLogBudget P) :
    (adaptiveAffineShell A sourceDim siteDim epsilon L T C totalShell modLog)⁻¹ ≤
      Real.exp (affineShellLogBudget P) := by
  simp only [adaptiveAffineShell, mul_inv_rev, ← Real.exp_neg, neg_neg]
  calc
    _ ≤ Real.exp (affineCountLogBudget P) * Real.exp P :=
      mul_le_mul (Real.exp_le_exp.mpr hcount) htotalInv (inv_nonneg.mpr htotal.le) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; unfold affineShellLogBudget; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffineSidePolynomialBudget
namespace OAI

section

namespace Erdos3

theorem affineDegreeBudgets_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ affineLocalDegreeInputBudget P ∧ 0 ≤ affineOuterDegreeInputBudget P ∧
      0 ≤ affineLocalDegreeBudget P ∧ 0 ≤ affineAdaptiveDegreeBudget P := by
  have hH := affinePrimitiveLogBudget_nonneg hP
  have hS := (affineShellLogBudget_nonneg hP).2
  simp only [affineLocalDegreeInputBudget, affineOuterDegreeInputBudget, affineLocalDegreeBudget, affineAdaptiveDegreeBudget]
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

theorem affineComparisonDegree_le_polynomialBudget (sourceDim siteDim : ℕ)
    {epsilon L T C shell modLog P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmod0 : 0 ≤ modLog)
    (hLP : L ≤ P) (hTP : T ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hmod : modLog ≤ P) (hshell : 0 < shell) (hshellInv : shell⁻¹ ≤ Real.exp (affineShellLogBudget P))
    (hsum : ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤ affinePrimitiveLogBudget P)
    (hscale : affineComparisonScale epsilon L T C ≤ affinePrimitiveLogBudget P) :
    (affineComparisonDegree sourceDim siteDim epsilon L T C shell modLog : ℝ) ≤ affineLocalDegreeBudget P := by
  let j := affineRemovalDepth T
  let tail := affineComparisonTail epsilon L T
  let scale := affineComparisonScale epsilon L T C
  let input := (j : ℝ) * (scale + (sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 2) +
    epsilon + L + 2 * T + 10
  have hscale0 : 0 ≤ scale := (affineComparisonScale_bounds (ε := epsilon) hL hT hC).1
  have hH := affinePrimitiveLogBudget_nonneg hP
  have hj : (j : ℝ) ≤ affinePrimitiveLogBudget P :=
    (Nat.cast_le.mpr (Nat.le_add_right j tail)).trans hsum
  have hs := mul_le_mul hsource hmod hmod0 hP
  have ht := mul_le_mul hsite hmod hmod0 hP
  have hinner : scale + (sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 2 ≤
      affinePrimitiveLogBudget P + 2 * P ^ 2 + 2 := by dsimp only [scale]; nlinarith
  have hmul := mul_le_mul hj hinner (by positivity) hH
  have hinput : input ≤ affineLocalDegreeInputBudget P := by
    dsimp only [input, affineLocalDegreeInputBudget]
    linarith
  have hinput0 : 0 ≤ input := by dsimp only [input]; positivity
  have hiter := CyclicCrootSisask.spectralIterations_le_logBudget hshell hinput0
    (affineShellLogBudget_nonneg hP).2 hshellInv
  have hiter' : (CyclicCrootSisask.spectralIterations shell input : ℝ) ≤
      2 * (affineLocalDegreeInputBudget P + affineShellLogBudget P + 4) + 2 := by linarith
  have hn : affineComparisonDegree sourceDim siteDim epsilon L T C shell modLog ≤
      j + tail + CyclicCrootSisask.spectralIterations shell input := by
    dsimp only [affineComparisonDegree, affineFinalDegree, j, tail, input, scale]
    omega
  calc
    _ ≤ ((j + tail : ℕ) : ℝ) + (CyclicCrootSisask.spectralIterations shell input : ℝ) := by exact_mod_cast hn
    _ ≤ affinePrimitiveLogBudget P + (2 * (affineLocalDegreeInputBudget P + affineShellLogBudget P + 4) + 2) :=
      add_le_add hsum hiter'
    _ = _ := by unfold affineLocalDegreeBudget; ring

theorem affineGlobalComparisonDegree_le_polynomialBudget (A sourceDim siteDim : ℕ)
    {epsilon L T C shell modLog P : ℝ} (hP : 0 ≤ P) (hmod0 : 0 ≤ modLog)
    (hA : (A : ℝ) ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hmod : modLog ≤ P) (hshell : 0 < shell) (hshellInv : shell⁻¹ ≤ Real.exp (affineShellLogBudget P))
    (hlocal : (affineComparisonDegree sourceDim siteDim epsilon L T C shell modLog : ℝ) ≤ affineLocalDegreeBudget P) :
    (affineGlobalComparisonDegree A sourceDim siteDim epsilon L T C shell modLog 0 : ℝ) ≤
      affineAdaptiveDegreeBudget P := by
  let input := (A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4
  have hs := mul_le_mul hsource hmod hmod0 hP
  have ht := mul_le_mul hsite hmod hmod0 hP
  have hi : (sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1 ≤ 2 * P ^ 2 + 1 := by nlinarith
  have hm := mul_le_mul hA hi (by positivity) hP
  have hinput : input ≤ affineOuterDegreeInputBudget P := by
    dsimp only [input, affineOuterDegreeInputBudget]
    linarith
  have hinput0 : 0 ≤ input := by dsimp only [input]; positivity
  have hiter := CyclicCrootSisask.spectralIterations_le_logBudget hshell hinput0
    (affineShellLogBudget_nonneg hP).2 hshellInv
  have hiter' : (CyclicCrootSisask.spectralIterations shell input : ℝ) ≤
      2 * (affineOuterDegreeInputBudget P + affineShellLogBudget P + 4) + 2 := by linarith
  have hn : affineGlobalComparisonDegree A sourceDim siteDim epsilon L T C shell modLog 0 ≤
      A + affineComparisonDegree sourceDim siteDim epsilon L T C shell modLog +
        CyclicCrootSisask.spectralIterations shell input := by
    dsimp only [affineGlobalComparisonDegree, input]
    simp only [add_zero]
    omega
  calc
    _ ≤ (A : ℝ) + (affineComparisonDegree sourceDim siteDim epsilon L T C shell modLog : ℝ) +
        (CyclicCrootSisask.spectralIterations shell input : ℝ) := by exact_mod_cast hn
    _ ≤ P + affineLocalDegreeBudget P + (2 * (affineOuterDegreeInputBudget P + affineShellLogBudget P + 4) + 2) :=
      add_le_add (add_le_add hA hlocal) hiter'
    _ = _ := by unfold affineAdaptiveDegreeBudget; ring

theorem adaptiveAffineCutoff_le_polynomialBudget (A sourceDim siteDim : ℕ)
    {epsilon L T C totalShell modLog P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmod0 : 0 ≤ modLog)
    (hLP : L ≤ P) (hTP : T ≤ P) (hCP : C ≤ P) (hmod : modLog ≤ P)
    (hA : (A : ℝ) ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hinverse : epsilon⁻¹ ≤ Real.exp P) (htotal : 0 < totalShell) (htotalInv : totalShell⁻¹ ≤ Real.exp P) :
    (adaptiveAffineCutoff A sourceDim siteDim epsilon L T C totalShell modLog : ℝ) ≤
      affineAdaptiveDegreeBudget P := by
  have hp := affineComparisonPrimitive_bounds hepsilon hepsilon1 hP hL hT hC hLP hTP hCP hinverse
  have hcount := adaptiveAffineCountLog_le_budget A sourceDim siteDim hP hmod0 hA hsource hsite hmod
    (affineComparisonScale_bounds (ε := epsilon) hL hT hC).1 hp.2.1
  have hs := adaptiveAffineShell_pos A sourceDim siteDim epsilon L T C modLog htotal
  have hsinv := adaptiveAffineShell_inverse_le_budget A sourceDim siteDim htotal htotalInv hcount
  have hlocal := affineComparisonDegree_le_polynomialBudget sourceDim siteDim hepsilon hepsilon1 hP
    hL hT hC hmod0 hLP hTP hsource hsite hmod hs hsinv hp.1 hp.2.1
  exact affineGlobalComparisonDegree_le_polynomialBudget A sourceDim siteDim hP hmod0 hA hsource hsite
    hmod hs hsinv hlocal

end Erdos3

end

section

namespace Erdos3

theorem affineComparisonRequiredOrder_le_budget (b : ℕ) {epsilon L T C P : ℝ}
    (hP : 0 ≤ P) (hb : (b : ℝ) ≤ affineAdaptiveDegreeBudget P)
    (hsum : ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤ affinePrimitiveLogBudget P)
    (hmoment : (affineComparisonMoment (affineComparisonScale epsilon L T C) : ℝ) ≤ affinePrimitiveLogBudget P + 2) :
    (affineComparisonRequiredOrder b epsilon L T C : ℝ) ≤ affineOrderPolynomialBudget P := by
  have hH := affinePrimitiveLogBudget_nonneg hP
  have hB := (affineDegreeBudgets_nonneg hP).2.2.2
  have hj : (affineRemovalDepth T : ℝ) ≤ affinePrimitiveLogBudget P :=
    (Nat.cast_le.mpr (Nat.le_add_right (affineRemovalDepth T) (affineComparisonTail epsilon L T))).trans hsum
  unfold affineComparisonRequiredOrder
  rw [Nat.cast_max]
  apply max_le
  · have hm := mul_le_mul hsum (add_le_add hmoment (le_refl (1 : ℝ)))
      (by positivity) hH
    push_cast at hm ⊢
    unfold affineOrderPolynomialBudget
    nlinarith
  · push_cast
    unfold affineOrderPolynomialBudget
    nlinarith [mul_nonneg hH (by linarith : 0 ≤ affinePrimitiveLogBudget P + 3)]

theorem affineComparisonAccuracyLog_le_budget (b : ℕ) {epsilon L T C P : ℝ}
    (hP : 0 ≤ P) (hb : (b : ℝ) ≤ affineAdaptiveDegreeBudget P)
    (hscale0 : 0 ≤ affineComparisonScale epsilon L T C)
    (hscale : affineComparisonScale epsilon L T C ≤ affinePrimitiveLogBudget P)
    (hLP : L ≤ P) (hTP : T ≤ P) :
    affineComparisonAccuracyLog b (affineComparisonScale epsilon L T C) L T ≤ affineAccuracyPolynomialBudget P := by
  have hB := (affineDegreeBudgets_nonneg hP).2.2.2
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ affineComparisonScale epsilon L T C + 3)
    (add_le_add hscale (le_refl (3 : ℝ))) 3
  have hm := mul_le_mul hb (add_le_add hscale (le_refl (2 : ℝ))) (by linarith) hB
  unfold affineComparisonAccuracyLog affineAccuracyPolynomialBudget
  nlinarith

theorem adaptiveAffineSideLog_le_polynomialBudget (A sourceDim siteDim : ℕ)
    {epsilon L T C totalShell modLog dimLog P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmod0 : 0 ≤ modLog)
    (hLP : L ≤ P) (hTP : T ≤ P) (hCP : C ≤ P) (hmod : modLog ≤ P) (hdim : dimLog ≤ P)
    (hA : (A : ℝ) ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hinverse : epsilon⁻¹ ≤ Real.exp P) (htotal : 0 < totalShell) (htotalInv : totalShell⁻¹ ≤ Real.exp P) :
    adaptiveAffineSideLog A sourceDim siteDim epsilon L T C totalShell modLog dimLog ≤
      affineSidePolynomialBudget P := by
  let b := adaptiveAffineCutoff A sourceDim siteDim epsilon L T C totalShell modLog
  have hb : (b : ℝ) ≤ affineAdaptiveDegreeBudget P :=
    adaptiveAffineCutoff_le_polynomialBudget A sourceDim siteDim hepsilon hepsilon1 hP hL hT hC hmod0
      hLP hTP hCP hmod hA hsource hsite hinverse htotal htotalInv
  have hp := affineComparisonPrimitive_bounds hepsilon hepsilon1 hP hL hT hC hLP hTP hCP hinverse
  have ho := affineComparisonRequiredOrder_le_budget b hP hb hp.1 hp.2.2
  have ha := affineComparisonAccuracyLog_le_budget b hP hb
    (affineComparisonScale_bounds (ε := epsilon) hL hT hC).1 hp.2.1 hLP hTP
  have hm := mul_le_mul hmod hA (Nat.cast_nonneg A) hP
  have horder := mul_le_mul hmod ho (Nat.cast_nonneg _) hP
  change modLog * A +
    (modLog * (affineComparisonRequiredOrder b epsilon L T C : ℝ) +
      affineComparisonAccuracyLog b (affineComparisonScale epsilon L T C) L T + dimLog + 1) + 2 ≤ _
  unfold affineSidePolynomialBudget
  nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCommonReferenceBudget
namespace OAI

section

namespace Erdos3

theorem affineSidePolynomialBudget_le_power {P : ℝ} (hP : 0 ≤ P) :
    affineSidePolynomialBudget P ≤ 65536 * (P + 3) ^ 4 := by
  apply le_of_sub_nonneg
  simp only [affineSidePolynomialBudget, affineOrderPolynomialBudget, affineAccuracyPolynomialBudget,
    affineAdaptiveDegreeBudget, affineLocalDegreeBudget, affineOuterDegreeInputBudget,
    affineLocalDegreeInputBudget, affineShellLogBudget, affineCountLogBudget, affinePrimitiveLogBudget]
  ring_nf
  positivity

theorem adaptiveAffineSideLog_le_power (A sourceDim siteDim : ℕ)
    {epsilon L T C totalShell modLog dimLog P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmod0 : 0 ≤ modLog)
    (hLP : L ≤ P) (hTP : T ≤ P) (hCP : C ≤ P) (hmod : modLog ≤ P) (hdim : dimLog ≤ P)
    (hA : (A : ℝ) ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hinverse : epsilon⁻¹ ≤ Real.exp P) (htotal : 0 < totalShell) (htotalInv : totalShell⁻¹ ≤ Real.exp P) :
    adaptiveAffineSideLog A sourceDim siteDim epsilon L T C totalShell modLog dimLog ≤
      65536 * (P + 3) ^ 4 :=
  (adaptiveAffineSideLog_le_polynomialBudget A sourceDim siteDim hepsilon hepsilon1 hP hL hT hC hmod0
    hLP hTP hCP hmod hdim hA hsource hsite hinverse htotal htotalInv).trans (affineSidePolynomialBudget_le_power hP)

end Erdos3

end

section

namespace Erdos3

theorem adaptiveAffineSideLog_reference_bound {E sourceDim siteDim : ℕ}
    {epsilon L T C totalShell modLog dimLog U : ℝ}
    (hE : 2 ≤ E) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hU : 0 ≤ U)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmod0 : 0 ≤ modLog)
    (hLU : L ≤ U) (hTU : T ≤ U) (hCU : C ≤ U) (hmod : modLog ≤ U) (hdim : dimLog ≤ U)
    (hsource : (sourceDim : ℝ) ≤ U) (hsite : (siteDim : ℝ) ≤ U)
    (hinverse : epsilon⁻¹ ≤ Real.exp U) (htotal : 0 < totalShell) (htotalInv : totalShell⁻¹ ≤ Real.exp U) :
    adaptiveAffineSideLog ⌈(affineReferenceInput epsilon U + 2) ^ E⌉₊ sourceDim siteDim
      epsilon L T C totalShell modLog dimLog ≤ 65536 * (affineCommonReferenceBudget E epsilon U + 3) ^ 4 := by
  have hc := affineCommonReferenceBudget_bounds hE epsilon hU
  have he : Real.exp U ≤ Real.exp (affineCommonReferenceBudget E epsilon U) := Real.exp_le_exp.mpr hc.2.1
  exact adaptiveAffineSideLog_le_power _ sourceDim siteDim hepsilon hepsilon1 hc.1 hL hT hC hmod0
    (hLU.trans hc.2.1) (hTU.trans hc.2.1) (hCU.trans hc.2.1) (hmod.trans hc.2.1) (hdim.trans hc.2.1)
    hc.2.2 (hsource.trans hc.2.1) (hsite.trans hc.2.1) (hinverse.trans he) htotal (htotalInv.trans he)

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.adaptiveAffineSideLog_reference_bound := @OAI.Erdos3.adaptiveAffineSideLog_reference_bound
