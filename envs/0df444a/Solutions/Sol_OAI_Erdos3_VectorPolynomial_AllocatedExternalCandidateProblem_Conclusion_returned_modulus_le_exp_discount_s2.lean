-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.returned_modulus_le_exp_discount_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:55:03.279751+00:00
-- url     : https://prove2.me/submissions/528a0744-19e8-4fb1-ab39-f38575f8bb88

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B303

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RetainedPatchCutoffChoice
namespace OAI

section

namespace Erdos3

theorem retainedPatchCutoffChoice_bounds {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    retainedPatchRelativeError ε ∈ Set.Icc (0 : ℝ) 1 ∧
    0 < retainedPatchCutoff ε ∧
    2 / (retainedPatchCutoff ε : ℝ) ≤ 1 / 2 ∧
    4 / (retainedPatchCutoff ε : ℝ) ≤ retainedPatchRelativeError ε ∧
    (1 + retainedPatchRelativeError ε) * (1 - ε) ≤ 1 - retainedPatchRelativeError ε ∧
    (retainedPatchCutoff ε : ℝ) ≤ 16 / ε + 1 ∧
    (retainedPatchCutoff ε : ℝ) ≤ 17 / ε := by
  have hlo : 16 / ε ≤ (retainedPatchCutoff ε : ℝ) := Nat.le_ceil _
  have hpos : 0 < retainedPatchCutoff ε := Nat.ceil_pos.mpr (by positivity)
  have hposr : (0 : ℝ) < retainedPatchCutoff ε := Nat.cast_pos.mpr hpos
  have hprod : 16 ≤ (retainedPatchCutoff ε : ℝ) * ε := (div_le_iff₀ hε).mp hlo
  have hsixteen : (16 : ℝ) ≤ retainedPatchCutoff ε :=
    ((le_div_iff₀ hε).mpr (by nlinarith)).trans hlo
  have hupp : (retainedPatchCutoff ε : ℝ) ≤ 16 / ε + 1 :=
    (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 16 / ε)).le
  refine ⟨⟨by unfold retainedPatchRelativeError; positivity,
    by unfold retainedPatchRelativeError; linarith⟩, hpos, ?_, ?_, ?_, hupp, ?_⟩
  · apply (div_le_iff₀ hposr).mpr
    linarith
  · apply (div_le_iff₀ hposr).mpr
    unfold retainedPatchRelativeError
    nlinarith only [hprod]
  · unfold retainedPatchRelativeError
    nlinarith [sq_nonneg ε]
  · apply hupp.trans
    apply (le_div_iff₀ hε).mpr
    have hcancel : (16 / ε : ℝ) * ε = 16 := div_mul_cancel₀ _ hε.ne'
    nlinarith only [hcancel, hεone]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.InjectiveSmallPrimeProduct
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem card_filter_le_cutoff_of_injective
    {L : Type*} [Fintype L] (p : L → ℕ) (hp : Function.Injective p)
    (cutoff : ℕ) :
    (Finset.univ.filter (fun l => p l ≤ cutoff)).card ≤ cutoff + 1 := by
  classical
  have hcard := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter (fun l => p l ≤ cutoff))
    (t := Finset.range (cutoff + 1)) p
    (fun l hl => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.mem_filter.mp hl).2))
    (fun _ _ _ _ heq => hp heq)
  simpa only [Finset.card_range] using hcard

theorem prod_filter_le_cutoff_pow_of_injective
    {L : Type*} [Fintype L] (p : L → ℕ) (hp : Function.Injective p)
    (cutoff : ℕ) :
    (∏ l ∈ Finset.univ.filter (fun l => p l ≤ cutoff), p l) ≤
      (cutoff + 1) ^ (cutoff + 1) := by
  classical
  calc
    _ ≤ (cutoff + 1) ^ (Finset.univ.filter (fun l => p l ≤ cutoff)).card :=
      Finset.prod_le_pow_card _ p (cutoff + 1)
        (fun l hl => (Finset.mem_filter.mp hl).2.trans (Nat.le_succ cutoff))
    _ ≤ _ := Nat.pow_le_pow_right (Nat.succ_pos cutoff)
      (card_filter_le_cutoff_of_injective p hp cutoff)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeDepthBudget
namespace OAI

section

namespace Erdos3

theorem natLog_ceil_exp_le_linear {p : ℕ} (hp : 2 ≤ p)
    {B : ℝ} (hB : 0 ≤ B) :
    (Nat.log p ⌈Real.exp B⌉₊ : ℝ) ≤ 2 * B + 2 := by
  let Q : ℕ := ⌈Real.exp B⌉₊
  let n : ℕ := Nat.log p Q
  have hQ : 0 < Q := Nat.ceil_pos.mpr (Real.exp_pos B)
  have hpowNat : 2 ^ n ≤ Q :=
    (Nat.pow_le_pow_left hp n).trans (Nat.pow_log_le_self p hQ.ne')
  have hpow : (2 : ℝ) ^ n ≤ Q := by exact_mod_cast hpowNat
  have hceil : (Q : ℝ) ≤ 2 * Real.exp B := by
    have hc := Nat.ceil_lt_add_one (Real.exp_pos B).le
    have he : 1 ≤ Real.exp B := Real.one_le_exp_iff.mpr hB
    dsimp [Q]
    linarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ n)
    (hpow.trans hceil)
  rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (Real.exp_ne_zero B), Real.log_exp] at hlog
  have hhalf : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hone : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  dsimp [n, Q] at hlog hn ⊢
  nlinarith

theorem prime_natLog_tested_depth_le {p : ℕ} (hp : p.Prime)
    {Ptest : ℝ} (hPtest : 0 ≤ Ptest) :
    (Nat.log p ⌈Real.exp (2 * Ptest)⌉₊ : ℝ) ≤ 4 * Ptest + 2 := by
  have h := natLog_ceil_exp_le_linear hp.two_le
    (B := 2 * Ptest) (mul_nonneg (by norm_num) hPtest)
  nlinarith

theorem exists_testedPrimeDepth {Ptest : ℝ} (hPtest : 0 ≤ Ptest) :
    ∃ depth : ℕ, (depth : ℝ) ≤ 4 * Ptest + 2 ∧
      ∀ p : ℕ, p.Prime → Nat.log p ⌈Real.exp (2 * Ptest)⌉₊ ≤ depth := by
  have hnonneg : 0 ≤ 4 * Ptest + 2 := by positivity
  refine ⟨⌊4 * Ptest + 2⌋₊, Nat.floor_le hnonneg, ?_⟩
  intro p hp
  exact Nat.le_floor (prime_natLog_tested_depth_le hp hPtest)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ActualFixedSpatialUnchargedDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in

theorem referenceBadDepth_product_le :
    (∏ p : path.primes, p.val ^ path.referenceBadDepth p.val) ≤ path.Rbad := by
  exact path.hbad

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ActualFixedSpatialGoodPrimeDeletion
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem retainedPrimeProduct_le_chargedProduct_mul_smallProduct
    {L : Type*} [Fintype L] (p b e : L → ℕ) (cutoff : ℕ)
    (hp : ∀ l, 1 ≤ p l) (retained : Finset L)
    (hretained : ∀ l ∈ retained, b l ≠ 0 ∨ e l ≠ 0 ∨ p l ≤ cutoff) :
    (∏ l ∈ retained, p l) ≤
      ((∏ l, p l ^ b l) * (∏ l, p l ^ e l)) *
        ∏ l ∈ Finset.univ.filter (fun l => p l ≤ cutoff), p l := by
  let w (l : L) := (p l ^ b l * p l ^ e l) * (if p l ≤ cutoff then p l else 1)
  have hw (l : L) : 1 ≤ w l := by
    dsimp only [w]
    apply one_le_mul
    · exact one_le_mul (one_le_pow₀ (hp l)) (one_le_pow₀ (hp l))
    · split_ifs
      · exact hp l
      · exact le_rfl
  have hpoint (l : L) (hl : l ∈ retained) : p l ≤ w l := by
    have hb1 : 1 ≤ p l ^ b l := one_le_pow₀ (hp l)
    have he1 : 1 ≤ p l ^ e l := one_le_pow₀ (hp l)
    dsimp only [w]
    by_cases hsmall : p l ≤ cutoff
    · simp only [hsmall, ite_true]
      exact le_mul_of_one_le_left' (one_le_mul hb1 he1)
    · simp only [hsmall, ite_false, mul_one]
      rcases hretained l hl with hb | he | hs
      · exact (le_self_pow (hp l) hb).trans (le_mul_of_one_le_right' he1)
      · exact (le_self_pow (hp l) he).trans (le_mul_of_one_le_left' hb1)
      · exact (hsmall hs).elim
  calc
    (∏ l ∈ retained, p l) ≤ ∏ l ∈ retained, w l :=
      Finset.prod_le_prod' hpoint
    _ ≤ ∏ l, w l := Finset.prod_le_prod_of_subset_of_one_le'
      (Finset.subset_univ _) (fun l _ _ => hw l)
    _ = ((∏ l, p l ^ b l) * (∏ l, p l ^ e l)) *
        ∏ l ∈ Finset.univ.filter (fun l => p l ≤ cutoff), p l := by
      simp only [w, Finset.prod_mul_distrib, Finset.prod_filter]

theorem retainedPrimePowerModulus_le_power_of_primeProduct
    {L : Type*} [Fintype L] (p A : L → ℕ) (retained : Finset L)
    (depth : ℕ) (hp : ∀ l, 1 ≤ p l) (hA : ∀ l ∈ retained, A l ≤ depth) :
    (∏ l ∈ retained, p l ^ A l) ≤ (∏ l ∈ retained, p l) ^ depth := by
  calc
    (∏ l ∈ retained, p l ^ A l) ≤ ∏ l ∈ retained, p l ^ depth :=
      Finset.prod_le_prod' (fun l hl => pow_le_pow_right' (hp l) (hA l hl))
    _ = (∏ l ∈ retained, p l) ^ depth := Finset.prod_pow _ _ _

theorem retainedPrimePowerModulus_le_charged_cutoff
    {L : Type*} [Fintype L] (p A b e : L → ℕ) (cutoff depth : ℕ)
    (hp : ∀ l, 1 ≤ p l) (hinj : Function.Injective p)
    (retained : Finset L)
    (hretained : ∀ l ∈ retained, b l ≠ 0 ∨ e l ≠ 0 ∨ p l ≤ cutoff)
    (hA : ∀ l ∈ retained, A l ≤ depth) :
    (∏ l ∈ retained, p l ^ A l) ≤
      ((∏ l, p l ^ b l) * (∏ l, p l ^ e l) *
        (cutoff + 1) ^ (cutoff + 1)) ^ depth := by
  have hprime : (∏ l ∈ retained, p l) ≤
      (∏ l, p l ^ b l) * (∏ l, p l ^ e l) * (cutoff + 1) ^ (cutoff + 1) :=
    (retainedPrimeProduct_le_chargedProduct_mul_smallProduct
      p b e cutoff hp retained hretained).trans
        (Nat.mul_le_mul_left _ (prod_filter_le_cutoff_pow_of_injective p hinj cutoff))
  exact (retainedPrimePowerModulus_le_power_of_primeProduct
    p A retained depth hp hA).trans (pow_le_pow_left' hprime depth)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem retainedPrimePowerModulus_le_exp_charged_cutoff
    {L : Type*} [Fintype L] (p A b e : L → ℕ) (cutoff depth : ℕ)
    (hp : ∀ l, 1 ≤ p l) (hinj : Function.Injective p)
    (retained : Finset L)
    (hretained : ∀ l ∈ retained, b l ≠ 0 ∨ e l ≠ 0 ∨ p l ≤ cutoff)
    (hA : ∀ l ∈ retained, A l ≤ depth) (Pbad Ppres : ℝ)
    (hbad : ((∏ l, p l ^ b l : ℕ) : ℝ) ≤ Real.exp Pbad)
    (hpres : ((∏ l, p l ^ e l : ℕ) : ℝ) ≤ Real.exp Ppres) :
    ((∏ l ∈ retained, p l ^ A l : ℕ) : ℝ) ≤
      Real.exp ((depth : ℝ) *
        (Pbad + Ppres + ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1))) := by
  have hcharged :
      (((∏ l, p l ^ b l) * (∏ l, p l ^ e l) *
        (cutoff + 1) ^ (cutoff + 1) : ℕ) : ℝ) ≤
      Real.exp (Pbad + Ppres +
        ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1)) := by
    calc
      _ = ((∏ l, p l ^ b l : ℕ) : ℝ) * ((∏ l, p l ^ e l : ℕ) : ℝ) *
          ((cutoff + 1 : ℕ) : ℝ) ^ (cutoff + 1) := by norm_cast
      _ ≤ Real.exp Pbad * Real.exp Ppres *
          ((cutoff + 1 : ℕ) : ℝ) ^ (cutoff + 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hbad hpres (Nat.cast_nonneg _) (Real.exp_nonneg _))
          (by positivity)
      _ = _ := by
        rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul,
          Real.exp_log (by positivity)]
        simp only [Nat.cast_add, Nat.cast_one]
  have hnat := retainedPrimePowerModulus_le_charged_cutoff
    p A b e cutoff depth hp hinj retained hretained hA
  calc
    _ ≤ (((∏ l, p l ^ b l) * (∏ l, p l ^ e l) *
          (cutoff + 1) ^ (cutoff + 1) : ℕ) : ℝ) ^ depth := by
      exact_mod_cast hnat
    _ ≤ Real.exp (Pbad + Ppres +
          ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1)) ^ depth :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hcharged depth
    _ = _ := (Real.exp_nat_mul _ depth).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem primePowerProduct_expBudget_nonneg
    {L : Type*} [Fintype L] (p b : L → ℕ) (hp : ∀ l, 1 ≤ p l)
    (P : ℝ) (hP : ((∏ l, p l ^ b l : ℕ) : ℝ) ≤ Real.exp P) : 0 ≤ P := by
  have hnat : 1 ≤ ∏ l, p l ^ b l :=
    Finset.one_le_prod' (fun l _ => one_le_pow₀ (hp l))
  have hreal : (1 : ℝ) ≤ ((∏ l, p l ^ b l : ℕ) : ℝ) := by exact_mod_cast hnat
  exact Real.one_le_exp_iff.mp (hreal.trans hP)

theorem retainedPrimePower_cutoff_logCost_nonneg (cutoff : ℕ) :
    0 ≤ ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1) := by
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Real.log_nonneg
  have hc : (0 : ℝ) ≤ cutoff := Nat.cast_nonneg cutoff
  linarith

theorem retainedPrimePowerModulus_le_exp_depthBudget
    {L : Type*} [Fintype L] (p A b e : L → ℕ) (cutoff depth : ℕ)
    (hp : ∀ l, 1 ≤ p l) (hinj : Function.Injective p)
    (retained : Finset L)
    (hretained : ∀ l ∈ retained, b l ≠ 0 ∨ e l ≠ 0 ∨ p l ≤ cutoff)
    (hA : ∀ l ∈ retained, A l ≤ depth) (Pbad Ppres Pdepth : ℝ)
    (hbad : ((∏ l, p l ^ b l : ℕ) : ℝ) ≤ Real.exp Pbad)
    (hpres : ((∏ l, p l ^ e l : ℕ) : ℝ) ≤ Real.exp Ppres)
    (hdepth : (depth : ℝ) ≤ Pdepth) :
    ((∏ l ∈ retained, p l ^ A l : ℕ) : ℝ) ≤
      Real.exp (Pdepth *
        (Pbad + Ppres + ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1))) := by
  have hcost : 0 ≤ Pbad + Ppres +
      ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1) :=
    add_nonneg (add_nonneg (primePowerProduct_expBudget_nonneg p b hp Pbad hbad)
      (primePowerProduct_expBudget_nonneg p e hp Ppres hpres))
      (retainedPrimePower_cutoff_logCost_nonneg cutoff)
  exact (retainedPrimePowerModulus_le_exp_charged_cutoff
    p A b e cutoff depth hp hinj retained hretained hA Pbad Ppres hbad hpres).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hdepth hcost))

theorem log_retainedPrimePowerModulus_le_depthBudget
    {L : Type*} [Fintype L] (p A b e : L → ℕ) (cutoff depth : ℕ)
    (hp : ∀ l, 1 ≤ p l) (hinj : Function.Injective p)
    (retained : Finset L)
    (hretained : ∀ l ∈ retained, b l ≠ 0 ∨ e l ≠ 0 ∨ p l ≤ cutoff)
    (hA : ∀ l ∈ retained, A l ≤ depth) (Pbad Ppres Pdepth : ℝ)
    (hbad : ((∏ l, p l ^ b l : ℕ) : ℝ) ≤ Real.exp Pbad)
    (hpres : ((∏ l, p l ^ e l : ℕ) : ℝ) ≤ Real.exp Ppres)
    (hdepth : (depth : ℝ) ≤ Pdepth) :
    Real.log ((∏ l ∈ retained, p l ^ A l : ℕ) : ℝ) ≤
      Pdepth * (Pbad + Ppres +
        ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1)) := by
  have hnat : 1 ≤ ∏ l ∈ retained, p l ^ A l :=
    Finset.one_le_prod' (fun l _ => one_le_pow₀ (hp l))
  have hreal : (1 : ℝ) ≤ ((∏ l ∈ retained, p l ^ A l : ℕ) : ℝ) := by
    exact_mod_cast hnat
  apply (Real.log_le_iff_le_exp (zero_lt_one.trans_le hreal)).mpr
  exact retainedPrimePowerModulus_le_exp_depthBudget
    p A b e cutoff depth hp hinj retained hretained hA Pbad Ppres Pdepth hbad hpres hdepth

theorem log_retainedPrimePowerModulus_filter_le_depthBudget
    {L : Type*} [Fintype L] (p A b e : L → ℕ) (cutoff depth : ℕ)
    (hp : ∀ l, 1 ≤ p l) (hinj : Function.Injective p)
    (hA : ∀ l, A l ≤ depth) (Pbad Ppres Pdepth : ℝ)
    (hbad : ((∏ l, p l ^ b l : ℕ) : ℝ) ≤ Real.exp Pbad)
    (hpres : ((∏ l, p l ^ e l : ℕ) : ℝ) ≤ Real.exp Ppres)
    (hdepth : (depth : ℝ) ≤ Pdepth) :
    Real.log ((∏ l ∈ Finset.univ.filter
        (fun l => b l ≠ 0 ∨ e l ≠ 0 ∨ p l ≤ cutoff), p l ^ A l : ℕ) : ℝ) ≤
      Pdepth * (Pbad + Ppres +
        ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1)) := by
  apply log_retainedPrimePowerModulus_le_depthBudget
    p A b e cutoff depth hp hinj _ _ _ Pbad Ppres Pdepth hbad hpres hdepth
  · intro l hl
    exact (Finset.mem_filter.mp hl).2
  · intro l _
    exact hA l

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.retainedReferencePrimeNeZero
attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.retainedReferenceModulusNeZero
omit [Fintype Tsp] in

theorem referenceRetainedModulus_log_le (cutoff depth : ℕ)
    (hdepth : ∀ p : path.primes, path.exponent p.val ≤ depth)
    (Pdepth : ℝ) (hPdepth : (depth : ℝ) ≤ Pdepth) :
    Real.log (path.referenceRetainedModulus cutoff : ℝ) ≤
      Pdepth * (Pbad + Ppres + ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1)) := by
  apply log_retainedPrimePowerModulus_filter_le_depthBudget
    (fun p : path.primes => p.val) (fun p : path.primes => path.exponent p.val)
    (fun p : path.primes => path.referenceBadDepth p.val)
    (fun p : path.primes => path.prescribed p.val) cutoff depth
    (fun p => (path.prime p.val p.property).one_le) Subtype.val_injective hdepth
    Pbad Ppres Pdepth
  · exact (Nat.cast_le.mpr path.referenceBadDepth_product_le).trans path.RbadBound
  · exact path.presBound
  · exact hPdepth

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialRetainedModulusBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in

theorem referenceRetainedCRTModulus_log_le_tested (cutoff : ℕ)
    {Ptest : ℝ} (hPtest : 0 ≤ Ptest)
    (hexponent : ∀ p : path.primes,
      path.exponent p.val ≤ Nat.log p.val ⌈Real.exp (2 * Ptest)⌉₊) :
    Real.log (path.referenceRetainedCRTModulus cutoff : ℝ) ≤
      (4 * Ptest + 2) *
        (Pbad + Ppres + ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1)) := by
  obtain ⟨depth, hdepth, hprime⟩ := exists_testedPrimeDepth hPtest
  rw [path.referenceRetainedCRTModulus_eq]
  exact path.referenceRetainedModulus_log_le cutoff depth
    (fun p => (hexponent p).trans (hprime p.val (path.prime p.val p.property)))
    (4 * Ptest + 2) hdepth

omit [Fintype Tsp] in

theorem referenceRetainedCRTModulus_le_exp_tested (cutoff : ℕ)
    {Ptest : ℝ} (hPtest : 0 ≤ Ptest)
    (hexponent : ∀ p : path.primes,
      path.exponent p.val ≤ Nat.log p.val ⌈Real.exp (2 * Ptest)⌉₊) :
    (path.referenceRetainedCRTModulus cutoff : ℝ) ≤
      Real.exp ((4 * Ptest + 2) *
        (Pbad + Ppres + ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1))) := by
  exact (Real.log_le_iff_le_exp
    (Nat.cast_pos.mpr (path.referenceRetainedCRTModulus_pos cutoff))).mp
      (path.referenceRetainedCRTModulus_log_le_tested cutoff hPtest hexponent)

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateReturnedModulusBudget
namespace OAI

section

namespace Erdos3

theorem retainedPatchModulusLog_le_cubic {ε B Ptest Pbad Ppres : ℝ}
    (hε : 0 < ε) (hεone : ε ≤ 1) (hB : 1 ≤ B)
    (hinv : ε⁻¹ ≤ B) (htest : Ptest ∈ Set.Icc 0 B)
    (hbad : Pbad ∈ Set.Icc 0 B) (hpres : Ppres ∈ Set.Icc 0 B) :
    (4 * Ptest + 2) * (Pbad + Ppres +
      ((retainedPatchCutoff ε + 1 : ℕ) : ℝ) * Real.log (retainedPatchCutoff ε + 1)) ≤
      2048 * B ^ 3 := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hBsq : B ≤ B ^ 2 := by nlinarith only [hB]
  have hcut : (retainedPatchCutoff ε : ℝ) ≤ 17 * B := by
    apply (retainedPatchCutoffChoice_bounds hε hεone).2.2.2.2.2.2.trans
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 17)
  let x : ℝ := (retainedPatchCutoff ε : ℝ) + 1
  have hx1 : 1 ≤ x := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hx : x ≤ 18 * B := by
    dsimp only [x]
    linarith only [hcut, hB]
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog : Real.log x ≤ 18 * B :=
    (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hx1)).trans
      ((sub_le_self x zero_le_one).trans hx)
  have hprod : x * Real.log x ≤ 324 * B ^ 2 := by
    calc
      _ ≤ (18 * B) * (18 * B) := mul_le_mul hx hlog hlog0 (by positivity)
      _ = _ := by ring
  have hsum0 : 0 ≤ Pbad + Ppres + x * Real.log x :=
    add_nonneg (add_nonneg hbad.1 hpres.1) (mul_nonneg hx0 hlog0)
  have hsum : Pbad + Ppres + x * Real.log x ≤ 326 * B ^ 2 := by
    linarith only [hbad.2, hpres.2, hprod, hBsq]
  have hfac : 4 * Ptest + 2 ≤ 6 * B := by linarith only [htest.2, hB]
  simp only [Nat.cast_add, Nat.cast_one]
  change (4 * Ptest + 2) * (Pbad + Ppres + x * Real.log x) ≤ _
  calc
    _ ≤ (6 * B) * (326 * B ^ 2) := mul_le_mul hfac hsum hsum0 (by positivity)
    _ ≤ 2048 * B ^ 3 := by nlinarith only [pow_nonneg hB0 3]

end Erdos3

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in

theorem referenceRetainedCRTModulus_le_exp_discount
    {ε budget Ptest : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    (hbudget : 1 ≤ budget) (hinv : ε⁻¹ ≤ budget)
    (htest : Ptest ∈ Set.Icc 0 budget)
    (hbad : Pbad ∈ Set.Icc 0 budget) (hpres : Ppres ∈ Set.Icc 0 budget)
    (hexponent : ∀ p : path.primes,
      path.exponent p.val ≤ Nat.log p.val ⌈Real.exp (2 * Ptest)⌉₊) :
    (path.referenceRetainedCRTModulus (retainedPatchCutoff ε) : ℝ) ≤
      Real.exp (2048 * budget ^ 3) :=
  (path.referenceRetainedCRTModulus_le_exp_tested (retainedPatchCutoff ε)
    htest.1 hexponent).trans (Real.exp_le_exp.mpr
      (retainedPatchModulusLog_le_cubic hε hεone hbudget hinv htest hbad hpres))

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix TensorProduct

variable {m : ℕ} {G X J₀ : Type} [Fintype G] [Fintype X]
variable (prep : RankPreparationFamily X J₀ m)
variable {preparationP : ℝ} {Rprep : ℕ}
variable (hprep : prep.PreparedHeights preparationP Rprep)
variable {I Eout : Fin m → Type} [∀ j, Fintype (I j)]
  [∀ j, Fintype (Eout j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {N : X → ℕ} {τ ξ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S Dmod (allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) τ (Real.exp (-cost) / 2))
variable (qnum : ActualFixedSpatialSlicedForecastNumerics s)
variable {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j))
  (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))]
variable {stride : X → ℕ}
variable {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) (fun j : Fin m => (prep j).space)}
variable {A : AllocatedExternalCandidateSampler B (fun j : Fin m => (prep j).space) b S hb o hR hσ N (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
  τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem.Conclusion
variable {Y M : Type} [LieRing M] [LieAlgebra ℚ M] {degree d t : ℕ}
variable (patch : PolynomialPatch Y degree d) [Fintype (PolynomialShearIndex patch.weight)]
variable {Fmark : NilpotentLieFiltration M t}
variable {φ : PolynomialShearLieAlgebra patch.weight ℚ →ₗ⁅ℚ⁆ M}
variable {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) (fun j : Fin m => (prep j).Coord))}
variable (f : (X → ℤ) → ℝ) (lam : ℝ)
variable {chartCost massThreshold scoreThreshold outputMass outputScore : ℝ}
variable {P : AllocatedExternalCandidateProblem (E := Eout) A
  (polynomialShearNilmanifold patch.weight degree patch.weight_le) Fmark φ marked
  (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
  chartCost massThreshold scoreThreshold}
variable (out : P.Conclusion cost outputMass outputScore)
variable {δbase PpresBase : ℝ}
variable (path : ∀ _z : out.retained, ActualFixedSpatialForecastPath (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S hR hσ Dmod spatial kernel block spatialEquiv
  (allocatedPhysicalRootBudget B (fun j : Fin m => (prep j).space) b S (fun _ => 0)) (S.value : ℝ) N τ δbase s.P s.Pbad PpresBase)
variable (hkeep : ∀ z : out.retained, ∀ k,
  (P.chart ⟨z.val, out.subset z.property⟩).keep k ↔ qnum.Hchild ≤ A.sides k)
variable (hkernel : Nonempty G) (hcutoff : qnum.Hchild ≤ S.value)
variable (hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ))
variable (hdensity : qnum.δ ≤ Real.exp (-cost)) (hlog : cost + 1 ≤ qnum.v)
variable (hprescribed : cost + 1 ≤ s.Ppres) (hstride : 2 * Real.exp cost ≤ qnum.Ptail)

local notation "input" z => out.denseSliceInput s qnum z (hkeep z) (ActualFixedSpatialForecastPath.commonTuple (path z))
  hkernel hcutoff hlate hdensity le_rfl hlog hprescribed hstride
local notation "member" z => ActualFixedSpatialForecastPath.toDenseSliceMember (path z) (input z)

omit [Fintype Tsp] in

theorem returned_modulus_le_exp_discount_s2_oai
    {ε budget Ptest : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    (hbudget : 1 ≤ budget) (hinv : ε⁻¹ ≤ budget)
    (htest : Ptest ∈ Set.Icc 0 budget)
    (hbad : s.Pbad ∈ Set.Icc 0 budget) (hpres : s.Ppres ∈ Set.Icc 0 budget)
    (hexponent : ∀ z, (path z).exponent = fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)
    (z : out.retained) :
    ((member z).slice.path.referenceRetainedCRTModulus (retainedPatchCutoff ε) : ℝ) ≤
      Real.exp (2048 * budget ^ 3) := by
  apply (member z).slice.path.referenceRetainedCRTModulus_le_exp_discount
    hε hεone hbudget hinv htest hbad hpres
  intro p
  change (path z).exponent p.val ≤ Nat.log p.val ⌈Real.exp (2 * Ptest)⌉₊
  rw [hexponent z]

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.returned_modulus_le_exp_discount_s2_oai := @OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.returned_modulus_le_exp_discount_s2_oai
