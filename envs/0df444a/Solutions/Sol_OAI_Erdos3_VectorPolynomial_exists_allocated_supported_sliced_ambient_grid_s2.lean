-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocated_supported_sliced_ambient_grid_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:46:25.458989+00:00
-- url     : https://prove2.me/submissions/24157b78-be5e-4e77-a2ad-be13f37eca71

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B196
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedFullGridDensity_mean_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights
open scoped Classical BigOperators NNReal

theorem mean_lipschitz_uniform {A X : Type*} [Fintype A] [PseudoMetricSpace X]
    (p : FiniteProbabilityWeights A) (f : A → X → ℝ) {L : ℝ≥0}
    (hf : ∀ a, LipschitzWith L (f a)) :
    LipschitzWith L (fun x => p.mean (fun a => f a x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    _ ≤ ∑ a, dist (p.weight a * f a x) (p.weight a * f a y) := dist_sum_sum_le _ _ _
    _ = ∑ a, p.weight a * dist (f a x) (f a y) := by
      simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (p.nonneg _)]
    _ ≤ ∑ a, p.weight a * ((L : ℝ) * dist x y) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left ((hf a).dist_le_mul _ _) (p.nonneg a))
    _ = _ := by rw [← Finset.sum_mul, p.total, one_mul]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {O : Type*} [Fintype O]

theorem integerRowMassTent_range {K : ℝ} (hK : 0 ≤ K) (z : O → ℤ) (x : O → ℝ) :
    0 ≤ integerRowMassTent K z x ∧ integerRowMassTent K z x ≤ K ^ Fintype.card O := by
  refine ⟨Finset.prod_nonneg (fun i _ => (integerMassTent_range K hK (z i) (x i)).1), ?_⟩
  simpa only [integerRowMassTent, Finset.prod_const, Finset.card_univ] using
    Finset.prod_le_prod (s := Finset.univ)
      (fun i _ => (integerMassTent_range K hK (z i) (x i)).1)
      (fun i _ => (integerMassTent_range K hK (z i) (x i)).2)

theorem integerRowMassTent_grid {K : ℝ} (hK : 0 < K) (z k : O → ℤ) :
    integerRowMassTent K z (fun i => (k i : ℝ) / K) =
      if z = k then K ^ Fintype.card O else 0 := by
  classical
  by_cases he : z = k
  · subst z
    simp [integerRowMassTent, integerMassTent_grid K hK]
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ k i := Function.ne_iff.mp he
    have hz : integerMassTent K (z i) ((k i : ℝ) / K) = 0 := by
      rw [integerMassTent_grid K hK]
      simp [Ne.symm hi]
    simp only [he, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz

theorem integerRowMassTent_lipschitz (K : ℝ≥0) (hK : 1 ≤ K) (z : O → ℤ) :
    LipschitzWith (Fintype.card O * (2 * K ^ 2) * K ^ Fintype.card O)
      (integerRowMassTent (K : ℝ) z) := by
  have hf (i : O) : LipschitzWith (2 * K ^ 2) (fun x : O → ℝ => integerMassTent K (z i) (x i)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      _ ≤ (2 * (K : ℝ) ^ 2) * |x i - y i| := integerMassTent_difference K K.coe_nonneg (z i) (x i) (y i)
      _ ≤ _ := by
        simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_pow, Real.dist_eq] using
          mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (by positivity : 0 ≤ 2 * (K : ℝ) ^ 2)
  exact (bounded_lipschitz_real_prod _ hK hf (fun i x => by
    rw [abs_of_nonneg (integerMassTent_range K K.coe_nonneg (z i) (x i)).1]
    exact (integerMassTent_range K K.coe_nonneg (z i) (x i)).2)).2

theorem integerRowMassTent_integrable {K : ℝ} (hK : 0 ≤ K) (p : PMF (O → ℤ)) (x : O → ℝ) :
    Integrable (fun z => integerRowMassTent K z x) p.toMeasure := by
  apply (integrable_const (K ^ Fintype.card O)).mono' (measurable_of_countable _).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (integerRowMassTent_range hK z x).1]
    exact (integerRowMassTent_range hK z x).2)

theorem integerRowMassInterpolation_range {K : ℝ} (hK : 0 ≤ K) (p : PMF (O → ℤ)) (x : O → ℝ) :
    0 ≤ integerRowMassInterpolation K p x ∧ integerRowMassInterpolation K p x ≤ K ^ Fintype.card O := by
  refine ⟨integral_nonneg (fun z => (integerRowMassTent_range hK z x).1), ?_⟩
  have h := integral_mono (integerRowMassTent_integrable hK p x) (integrable_const (K ^ Fintype.card O))
    (fun z => (integerRowMassTent_range hK z x).2)
  simpa only [integerRowMassInterpolation, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul] using h

theorem integerRowMassInterpolation_grid {K : ℝ} (hK : 0 < K) (p : PMF (O → ℤ)) (k : O → ℤ) :
    integerRowMassInterpolation K p (fun i => (k i : ℝ) / K) =
      K ^ Fintype.card O * (p k).toReal := by
  classical
  have he : (fun z => integerRowMassTent K z (fun i => (k i : ℝ) / K)) =
      Set.indicator {k} (fun _ => K ^ Fintype.card O) := by
    funext z
    simp only [integerRowMassTent_grid hK, Set.indicator_apply, Set.mem_singleton_iff]
  rw [integerRowMassInterpolation, he, integral_indicator (measurableSet_singleton k), integral_singleton,
    measureReal_def, PMF.toMeasure_apply_singleton _ k (measurableSet_singleton k), smul_eq_mul, mul_comm]

theorem integerRowMassInterpolation_lipschitz (K : ℝ≥0) (hK : 1 ≤ K) (p : PMF (O → ℤ)) :
    LipschitzWith (Fintype.card O * (2 * K ^ 2) * K ^ Fintype.card O)
      (integerRowMassInterpolation (K : ℝ) p) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖integerRowMassInterpolation (K : ℝ) p x - integerRowMassInterpolation (K : ℝ) p y‖ ≤ _
  rw [integerRowMassInterpolation, integerRowMassInterpolation,
    ← integral_sub (integerRowMassTent_integrable K.coe_nonneg p x) (integerRowMassTent_integrable K.coe_nonneg p y)]
  have h := norm_integral_le_of_norm_le_const (μ := p.toMeasure)
    (f := fun z => integerRowMassTent (K : ℝ) z x - integerRowMassTent (K : ℝ) z y)
    (C := (Fintype.card O * (2 * K ^ 2) * K ^ Fintype.card O : ℝ≥0) * dist x y)
    (Filter.Eventually.of_forall (fun z => by
      simpa only [dist_eq_norm] using (integerRowMassTent_lipschitz K hK z).dist_le_mul x y))
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using h

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {O : Type*} [Fintype O]

theorem normalizedIntegerRowInterpolation_range {K : ℝ} (hK : 0 < K)
    (p : PMF (O → ℤ)) (x : O → ℝ) :
    normalizedIntegerRowInterpolation K p x ∈ Set.Icc (0 : ℝ) 1 := by
  have h := integerRowMassInterpolation_range hK.le p x
  exact ⟨div_nonneg h.1 (pow_nonneg hK.le _), (div_le_one (pow_pos hK _)).mpr h.2⟩

theorem normalizedIntegerRowInterpolation_grid {K : ℝ} (hK : 0 < K)
    (p : PMF (O → ℤ)) (z : O → ℤ) :
    normalizedIntegerRowInterpolation K p (fun i => (z i : ℝ) / K) = (p z).toReal := by
  rw [normalizedIntegerRowInterpolation, integerRowMassInterpolation_grid hK]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ hK.ne')

theorem normalizedIntegerRowInterpolation_lipschitz (K : ℝ≥0) (hK : 1 ≤ K)
    (p : PMF (O → ℤ)) :
    LipschitzWith (Fintype.card O * (2 * K ^ 2)) (normalizedIntegerRowInterpolation K p) := by
  have hp : 0 < (K : ℝ) ^ Fintype.card O :=
    pow_pos (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hK)) _
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (integerRowMassInterpolation_lipschitz K hK p).dist_le_mul x y
  rw [Real.dist_eq] at h ⊢
  simp only [normalizedIntegerRowInterpolation, ← sub_div, abs_div, abs_of_pos hp]
  simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat, NNReal.coe_pow] at h ⊢
  apply (div_le_iff₀ hp).mpr
  calc
    _ ≤ (Fintype.card O * (2 * (K : ℝ) ^ 2) * (K : ℝ) ^ Fintype.card O) * dist x y := h
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

theorem integerMonomialArrayPolynomial_principal_sum {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (a : J → ℤ) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hzero : ∀ j, j ≠ j₀ → j ∉ P → a j = 0) :
    integerMonomialArrayPolynomial e a =
      MvPolynomial.C (a j₀) + ∑ j ∈ P, MvPolynomial.monomial (e j) (a j) := by
  classical
  have hsum : (∑ j ∈ insert j₀ P, MvPolynomial.monomial (e j) (a j)) =
      ∑ j, MvPolynomial.monomial (e j) (a j) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hne : j ≠ j₀ := fun he => hj (he ▸ Finset.mem_insert_self _ _)
    have hnot : j ∉ P := fun hp => hj (Finset.mem_insert_of_mem hp)
    simp [hzero j hne hnot]
  rw [integerMonomialArrayPolynomial, ← hsum, Finset.sum_insert hj₀, he₀]
  rfl

theorem productBlockExponent_monomial_int {V : Type*} {h : ℕ}
    (principal : Fin h → V) (c : ℤ) :
    MvPolynomial.monomial (productBlockExponent principal) c =
      MvPolynomial.C c * ∏ v, MvPolynomial.X (principal v) := by
  rw [productBlockExponent, MvPolynomial.monomial_sum_index]
  rfl

theorem integerPrincipalPolynomial_eval {D G : Type*} [Fintype D] [Fintype G]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (d : D) (hd : 0 < h d)
    (a : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → ℤ)
    (hzero : ∀ e, e ≠ constantCoefficientSlot _ _ → e ∉ principalCoefficientSlots h d → a e = 0)
    (x : SamplerTupleIndex G B h → ℤ) :
    MvPolynomial.eval x (integerMonomialArrayPolynomial Subtype.val a) =
      a (constantCoefficientSlot _ _) + ∑ b : B d,
        a (principalCoefficientSlot h d b) * ∏ v : Fin (h d), x (.inr ⟨d, b, v⟩) := by
  classical
  rw [integerMonomialArrayPolynomial_principal_sum Subtype.val a
    (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
    (constantCoefficientSlot_not_principal h d hd) rfl hzero]
  simp only [map_add, map_sum, MvPolynomial.eval_C]
  congr 1
  rw [principalCoefficientSlots, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro b _
    change MvPolynomial.eval x
      (MvPolynomial.monomial (productBlockExponent (fun v => .inr ⟨d, b, v⟩)) _) = _
    rw [productBlockExponent_monomial_int]
    simp only [map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  · intro b _ b' _ hb
    exact principalCoefficientSlot_injective h d hd hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedIntegerTailZero
namespace OAI

section

namespace Erdos3

section Coordinate

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
variable (hgap : L^h < K → (principalSamplingGapRatio (principalProfileSize R P.card)*L)^h ≤ K)
variable (hεL : 8*(probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J)*L)

local notation "laws" => allocatedIntegerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL
  e he R σ hR hσ hgap hεL

theorem allocatedIntegerCoordinate_tail_pure (hsmall : K ≤ L^(s+1))
    (j : J) (hj₀ : j ≠ j₀) (hjP : j ∉ P) : laws j = PMF.pure 0 := by
  classical
  unfold allocatedIntegerPolynomialCoordinatePMF integerPolynomialCoordinatePMF
  simp only [hj₀, hjP, ↓reduceIte]
  exact integerAxisTailPMF_small T hT hK hL hTL (tailProfileSize_pos hR hσ _) hεL (e j) (he j) hsmall

theorem allocatedIntegerCoordinate_tail_zero (hsmall : K ≤ L^(s+1))
    (j : J) (hj₀ : j ≠ j₀) (hjP : j ∉ P) {k : ℤ} (hk : k ∈ (laws j).support) : k = 0 := by
  rw [allocatedIntegerCoordinate_tail_pure P j₀ h K L s hh hK hL T hT hTL e he R σ hR hσ
    hgap hεL hsmall j hj₀ hjP] at hk
  simpa only [PMF.support_pure, Set.mem_singleton_iff] using hk

end Coordinate

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortDependence
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)

theorem allocatedLayerInteger_moderate_tail_zero
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (d : Slots) (hd₀ : d ≠ constantCoefficientSlot _ _)
    (hdP : d ∉ layerIntegerPrincipalSlots B j i) : a d = 0 := by
  exact allocatedIntegerCoordinate_tail_zero (layerIntegerPrincipalSlots B j i)
    (constantCoefficientSlot _ _) (j.val+1) (basisAxisScale (basis j) i) S.value (layerTailDegree m)
    (Nat.zero_lt_succ _) (basisAxisScale_pos (basis j) i) S.positive
    (layerSamplerBox B U basis S)
    (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
    (layerSamplerBox_le B U basis S) Subtype.val
    (fun e => e.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j i) (S.width j) hmoderate d hd₀ hdP (ha d)

theorem allocatedLayerInteger_moderate_eval
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (x : LayerSamplerVariables G I n B → ℤ) :
    MvPolynomial.eval x (integerMonomialArrayPolynomial Subtype.val a) =
      a (constantCoefficientSlot _ _) + ∑ b : B ⟨j, Sum.inr i⟩,
        a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) *
          ∏ v : Fin (j.val+1), x (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) := by
  exact integerPrincipalPolynomial_eval (layerSamplerDegree I n) ⟨j, Sum.inr i⟩
    (Nat.zero_lt_succ _) a
    (allocatedLayerInteger_moderate_tail_zero B U basis hR hσ S j i hmoderate a ha) x

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RealQuarterTorusExtension
namespace OAI

section

namespace Erdos3

theorem centeredCircleLift_dist {x y : AddCircle (1 : ℝ)}
    (hx : ‖x‖ ≤ 1 / 4) (hy : ‖y‖ ≤ 1 / 4) :
    dist (centeredCircleLift x) (centeredCircleLift y) = dist x y := by
  rw [norm_eq_abs_centeredCircleLift] at hx hy
  have hsmall : |centeredCircleLift x - centeredCircleLift y| ≤ 1 / 2 :=
    (abs_sub _ _).trans (by linarith)
  have he := (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num : (1 : ℝ) ≠ 0)).mpr
    (by simpa only [abs_one] using hsmall)
  calc
    dist (centeredCircleLift x) (centeredCircleLift y) =
        |centeredCircleLift x - centeredCircleLift y| := Real.dist_eq _ _
    _ = ‖((centeredCircleLift x - centeredCircleLift y : ℝ) : AddCircle (1 : ℝ))‖ := he.symm
    _ = dist x y := by rw [AddCircle.coe_sub, coe_centeredCircleLift, coe_centeredCircleLift, dist_eq_norm]

theorem centeredTorusLift_lipschitzOn {ι : Type*} [Fintype ι] :
    LipschitzOnWith 1 (centeredTorusLift (ι := ι))
      {x | ∀ i, ‖x i‖ ≤ 1 / 4} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff (dist_nonneg)).mpr
  intro i
  change dist (centeredCircleLift (x i)) (centeredCircleLift (y i)) ≤ dist x y
  rw [centeredCircleLift_dist (hx i) (hy i)]
  exact dist_le_pi_dist x y i

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_real_quarter_torus_extension {D : Type*} [Fintype D]
    (F : (D → ℝ) → ℝ) (L : ℝ≥0) (hL : LipschitzWith L F)
    (a b : ℝ) (hab : a ≤ b) (hF : ∀ v, F v ∈ Set.Icc a b) :
    ∃ g : (D → AddCircle (1 : ℝ)) → ℝ,
      LipschitzWith L g ∧ (∀ z, g z ∈ Set.Icc a b) ∧
        ∀ v : D → ℝ, (∀ i, |v i| ≤ 1 / 4) → g (fun i => (v i : AddCircle (1 : ℝ))) = F v := by
  let Q : Set (D → AddCircle (1 : ℝ)) := {z | ∀ i, ‖z i‖ ≤ 1 / 4}
  have hlocal : LipschitzOnWith L (fun z => F (centeredTorusLift z)) Q := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hdist : dist (centeredTorusLift x) (centeredTorusLift y) ≤ dist x y := by
      simpa only [NNReal.coe_one, one_mul] using centeredTorusLift_lipschitzOn.dist_le_mul x hx y hy
    exact (hL.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)
  obtain ⟨g, hg, heq, hgb⟩ := exists_real_lipschitz_extension_interval
    (fun z => F (centeredTorusLift z)) Q L hlocal a b hab (fun z _ => hF _)
  refine ⟨g, hg, hgb, ?_⟩
  intro v hv
  have hvQ : (fun i => (v i : AddCircle (1 : ℝ))) ∈ Q := by
    intro i
    rw [norm_eq_abs_centeredCircleLift, centeredCircleLift_coe (hv i)]
    exact hv i
  rw [← heq hvQ]
  apply congrArg F
  funext i
  exact centeredCircleLift_coe (hv i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

theorem allocatedPhysicalCube_vertex (t : Finset α) :
    integerAffineCube (allocatedPhysicalCubeRoot B U basis S c x y)
        (allocatedPhysicalCubeDirections B U basis S x y) t =
      fun k => c k + Sum.elim
        (fun g => integerScalarCubeValue (fun i => (x g i : ℤ)) t)
        (fun j => integerScalarCubeValue (fun i => (y j i : ℤ)) t) k := by
  funext k
  cases k <;> simp only [integerAffineCube, allocatedPhysicalCubeRoot,
    allocatedPhysicalCubeDirections, Sum.elim_inl, Sum.elim_inr, integerScalarCubeValue] <;> ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedWeightedGridMixture
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) ((j : ℕ) + 1)

theorem allocatedLayerInteger_moderate_jet_blocks
    (hmoderate : basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    {α O : Type*} [Fintype α] [DecidableEq α]
    (x : LayerSamplerVariables G I n B → Option α → ℤ)
    (rows : O → Finset α) (o : O) :
    (integerJetMatrix (fun d : Slots => MvPolynomial.monomial d.val (1 : ℤ))
      (fun t v => ∑ r, (booleanFeature r t : ℤ) * x v r) rows *ᵥ a) o =
      booleanCoefficient (fun _ => a (constantCoefficientSlot _ _)) (rows o) +
        ∑ b : B ⟨j, Sum.inr i⟩,
          a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) *
            integerBooleanBlockJet (fun v r => x (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) r) (rows o) := by
  simp only [integerJetMatrix_apply_coefficients, MvPolynomial.C_mul_monomial, mul_one]
  change booleanCoefficient (fun t => MvPolynomial.eval
      (fun v => ∑ r, (booleanFeature r t : ℤ) * x v r)
      (integerMonomialArrayPolynomial Subtype.val a)) (rows o) = _
  have he (t : Finset α) := allocatedLayerInteger_moderate_eval B U basis hR hσ S j i
    hmoderate a ha (fun v => ∑ r, (booleanFeature r t : ℤ) * x v r)
  simp_rw [he, booleanCoefficient_add, booleanCoefficient_sum, booleanCoefficient_const_mul]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) ((j : ℕ) + 1)

theorem allocatedPhysicalGridJet_blocks
    (hmoderate : basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    {α O : Type*} [Fintype α] [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (rows : O → Finset α) (o : O) :
    (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1) rows *ᵥ a) o =
      booleanCoefficient (fun _ => a (constantCoefficientSlot _ _)) (rows o) +
        ∑ b : B ⟨j, Sum.inr i⟩,
          a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) *
            integerBooleanBlockJet (fun v r => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ r : ℤ)) (rows o) := by
  let tuple : LayerSamplerVariables G I n B → Option α → ℤ := fun v r =>
    Sum.elim (fun g => (x g r : ℤ)) (fun q => (y q r : ℤ)) v
  have hvert : integerAffineCube (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) =
      (fun t v => ∑ r, (booleanFeature r t : ℤ) * tuple v r) := by
    funext t v
    rw [allocatedPhysicalCube_vertex]
    cases v <;> simp [tuple, integerScalarCubeValue, Fintype.sum_option, booleanFeature, ite_mul]
  change (integerJetMatrix (fun d : Slots => MvPolynomial.monomial d.val (1 : ℤ))
    (integerAffineCube (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y)) rows *ᵥ a) o = _
  rw [hvert]
  exact allocatedLayerInteger_moderate_jet_blocks B U basis hR hσ S j i hmoderate a ha tuple rows o

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

theorem allocatedPhysicalGridJetPMF_blocks
    (hmoderate : basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1))
    {α O : Type*} [Fintype α] [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (rows : O → Finset α) :
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1) rows)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i) =
      (independentProductPMF (allocatedLayerIntegerPMFs B U basis hR hσ S j i)).map
        (fun a o => booleanCoefficient (fun _ => a (constantCoefficientSlot _ _)) (rows o) +
          ∑ b : B ⟨j, Sum.inr i⟩,
            a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) *
              integerBooleanBlockJet (fun v r => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ r : ℤ)) (rows o)) := by
  unfold integerMatrixImagePMF
  ext z
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : independentProductPMF (allocatedLayerIntegerPMFs B U basis hR hσ S j i) a = 0
  · simp only [ha, ite_self]
  · have hs : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support := by
      intro d
      change allocatedLayerIntegerPMFs B U basis hR hσ S j i d (a d) ≠ 0
      rw [independentProductPMF_apply] at ha
      exact (Finset.prod_ne_zero_iff.mp ha) d (Finset.mem_univ d)
    have he := funext (fun o => allocatedPhysicalGridJet_blocks B U basis hR hσ S j i
      hmoderate a hs x y rows o)
    rw [he]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFrozenBlockPMF
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

omit [∀ j, Fintype (O j)] in
theorem allocatedGridJetFactor_frozen_blocks
    (x : G → IntegerScalarCubeBox α S.value)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U b S))
    (a : {a // grid a}) (z : CoefficientJetAxisRow O a.val) :
    allocatedGridJetFactor B U b hR hσ S x u v rows a z =
      (allocatedFrozenBlockPMF B U b hR hσ S u rows a z).toReal := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · have h := allocatedPhysicalGridJetPMF_blocks B U b hR hσ S j i ha x
      (principalAxisJoin grid u v) (rows j)
    have hjoin (q : B ⟨j, Sum.inr i⟩) (w : Fin (j.val + 1)) :
        principalAxisJoin grid u v ⟨⟨j, Sum.inr i⟩, q, w⟩ =
          u ⟨⟨⟨j, Sum.inr i⟩, ha⟩, q, w⟩ := by
      exact congrFun (principalAxisRestrict_join_left grid u v) ⟨⟨⟨j, Sum.inr i⟩, ha⟩, q, w⟩
    unfold allocatedGridJetFactor allocatedFrozenBlockPMF
    apply congrArg (fun p : PMF (O j → ℤ) => (p z).toReal)
    rw [h]
    congr 1
    funext c t
    apply congrArg (fun a : ℤ =>
      booleanCoefficient (fun _ => c (constantCoefficientSlot _ _)) (rows j t) + a)
    apply Finset.sum_congr rfl
    intro q _
    apply congrArg (fun a : ℤ => c (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ q) * a)
    apply congrArg (fun w => integerBooleanBlockJet w (rows j t))
    funext w r
    exact congrArg (fun y => (y r : ℤ)) (hjoin q w)

omit [∀ j, Fintype (O j)] in
theorem allocatedGridJetDensity_frozen_blocks
    (x : G → IntegerScalarCubeBox α S.value)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U b S))
    (z : AllocatedFrozenJetRows B U b S O) :
    allocatedGridJetDensity B U b hR hσ S x u v rows z =
      ∏ a, (allocatedFrozenBlockPMF B U b hR hσ S u rows a (z a)).toReal := by
  unfold allocatedGridJetDensity
  exact Finset.prod_congr rfl (fun a _ =>
    allocatedGridJetFactor_frozen_blocks B U b hR hσ S u rows x v a (z a))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedProbabilityGrid
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

theorem allocatedGridAxisScale_bounds (a : {a // grid a}) :
    1 ≤ allocatedGridAxisScale B U b S a ∧
      allocatedGridAxisScale B U b S a ≤ (S.value : ℝ≥0) ^ (layerTailDegree m + 1) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · constructor
    · change (1 : ℝ≥0) ≤ (basisAxisScale (b j) i : ℝ≥0)
      exact_mod_cast Nat.succ_le_of_lt (basisAxisScale_pos (b j) i)
    · change (basisAxisScale (b j) i : ℝ≥0) ≤ _
      change basisAxisScale (b j) i ≤ S.value ^ (layerTailDegree m + 1) at ha
      exact_mod_cast ha

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

omit [∀ j, Fintype (O j)] in
theorem allocatedGridAmbientCoordinates_point
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) :
    allocatedGridAmbientCoordinates B U b S o (mixedJetAmbientPoint U b o z) =
      allocatedGridNormalizedRows B U b S (fun a => coefficientJetAxisEquiv O I n z a.val) := by
  funext a t
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · change (mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j)
      ((EuclideanSpace.equiv (J j) ℝ).symm ((EuclideanSpace.equiv (J j) ℝ)
        (normalizedLatticePoint (euclideanSubspace (U j)) (b j)
          (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (z j) t)))))).2 i = _
    rw [ContinuousLinearEquiv.symm_apply_apply, mixedRealCoordinates_integer]
    rfl

theorem allocatedGridAmbientCoordinates_lipschitz (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖) :
    LipschitzWith (∑ j, C j * Fintype.card (J j)) (allocatedGridAmbientCoordinates B U b S (O := O) o) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  intro a
  apply (dist_pi_le_iff (by positivity)).mpr
  intro t
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · have hrow := ((mixedRealCoordinates_lipschitz (euclideanSubspace (U j)) (b j) (o j) (hC j)).comp
        (euclideanFromCoordinates_lipschitz (D := J j))).dist_le_mul
          (fun k => z ⟨j, t, k⟩) (fun k => w ⟨j, t, k⟩)
    have hin : dist (fun k => z ⟨j, t, k⟩) (fun k => w ⟨j, t, k⟩) ≤ dist z w :=
      (dist_pi_le_iff dist_nonneg).mpr (fun k => dist_le_pi_dist z w ⟨j, t, k⟩)
    let pz := mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j)
      ((EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, t, k⟩))
    let pw := mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j)
      ((EuclideanSpace.equiv (J j) ℝ).symm (fun k => w ⟨j, t, k⟩))
    have hout : dist (pz.2 i) (pw.2 i) ≤ dist pz pw :=
      (dist_le_pi_dist pz.2 pw.2 i).trans (le_max_right _ _)
    have hc : C j * Fintype.card (J j) ≤ ∑ j, C j * Fintype.card (J j) :=
      Finset.single_le_sum (f := fun k => C k * Fintype.card (J k))
        (fun _ _ => by positivity) (Finset.mem_univ j)
    exact (hout.trans hrow).trans ((mul_le_mul_of_nonneg_right
      (by exact_mod_cast hc) (dist_nonneg (x := z) (y := w))).trans'
        (mul_le_mul_of_nonneg_left hin (NNReal.coe_nonneg _)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

theorem allocatedNormalizedGridFactor_bounds (a : {a // grid a}) :
    (∀ z, allocatedNormalizedGridFactor B U b hR hσ S u rows a z ∈ Set.Icc (0 : ℝ) 1) ∧
    LipschitzWith (Fintype.card (O a.val.1) * (2 * allocatedGridAxisScale B U b S a ^ 2))
      (allocatedNormalizedGridFactor B U b hR hσ S u rows a) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact ⟨normalizedIntegerRowInterpolation_range (Nat.cast_pos.mpr (basisAxisScale_pos (b j) i)) _,
      normalizedIntegerRowInterpolation_lipschitz _ (allocatedGridAxisScale_bounds B U b S ⟨⟨j, .inr i⟩, ha⟩).1 _⟩

theorem allocatedNormalizedGridInterpolation_bounds (K : ℝ≥0) (D : ℕ)
    (hscale : ∀ a : {a // grid a}, allocatedGridAxisScale B U b S a ≤ K)
    (hD : ∀ a : {a // grid a}, Fintype.card (O a.val.1) ≤ D) :
    (∀ z, allocatedNormalizedGridInterpolation B U b hR hσ S u rows z ∈ Set.Icc (0 : ℝ) 1) ∧
    LipschitzWith (Fintype.card {a // grid a} * (D * (2 * K ^ 2)))
      (allocatedNormalizedGridInterpolation B U b hR hσ S u rows) := by
  have hb := allocatedNormalizedGridFactor_bounds B U b hR hσ S u rows
  have hl (a : {a // grid a}) : LipschitzWith (D * (2 * K ^ 2))
      (allocatedNormalizedGridFactor B U b hR hσ S u rows a) := by
    apply (hb a).2.weaken
    exact mul_le_mul (Nat.cast_le.mpr (hD a))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left' (hscale a) 2) (by positivity))
      (by positivity) (by positivity)
  have hc (a : {a // grid a}) : LipschitzWith (D * (2 * K ^ 2))
      (fun z : ∀ a : {a // grid a}, O a.val.1 → ℝ =>
        allocatedNormalizedGridFactor B U b hR hσ S u rows a (z a)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    exact ((hl a).dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist z w a) (NNReal.coe_nonneg _))
  obtain ⟨hbound, hLip⟩ := bounded_lipschitz_real_prod _ (B := 1) le_rfl hc
    (fun a z => by rw [abs_of_nonneg ((hb a).1 (z a)).1]; exact ((hb a).1 (z a)).2)
  refine ⟨fun z => ⟨Finset.prod_nonneg (fun a _ => ((hb a).1 (z a)).1), ?_⟩, ?_⟩
  · exact (le_abs_self _).trans (by
      simpa only [allocatedNormalizedGridInterpolation, NNReal.coe_one, one_pow] using hbound z)
  · apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [allocatedNormalizedGridInterpolation, one_pow, mul_one] using hLip.dist_le_mul z w

theorem allocatedNormalizedGridInterpolation_grid
    (x : G → IntegerScalarCubeBox α S.value)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U b S))
    (z : AllocatedFrozenJetRows B U b S O) :
    allocatedNormalizedGridInterpolation B U b hR hσ S u rows
        (allocatedGridNormalizedRows B U b S z) =
      allocatedGridJetDensity B U b hR hσ S x u v rows z := by
  rw [allocatedGridJetDensity_frozen_blocks B U b hR hσ S u rows x v z]
  unfold allocatedNormalizedGridInterpolation
  apply Finset.prod_congr rfl
  intro a _
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact normalizedIntegerRowInterpolation_grid (Nat.cast_pos.mpr (basisAxisScale_pos (b j) i)) _ _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.StandardJetFourier
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Classical

theorem euclideanAmbientTorus_normalized {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) {n : ℕ}
    (b : Basis (Fin n) ℝ (euclideanSubspace U)ᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice (euclideanSubspace U))
    (x : euclideanSubspace U × (Fin n → ℤ)) (i : D) :
    subspaceAmbientTorus U (euclideanSubspaceTorusEquiv U
      (normalizedLatticeQuotient (euclideanSubspace U) b hb x)) i =
        (normalizedLatticePoint (euclideanSubspace U) b x i : UnitAddCircle) := by
  let u := normalizedLatticeRepresentative (euclideanSubspace U) b hb x
  have hu : QuotientAddGroup.mk' _ u = normalizedLatticeQuotient (euclideanSubspace U) b hb x :=
    normalizedLatticeRepresentative_mk (euclideanSubspace U) b hb x
  rw [← hu, euclideanSubspaceTorusEquiv_mk, subspaceAmbientTorus_mk, euclideanSubspaceArrayEquiv_apply]
  apply sub_eq_zero.mp
  rw [← AddCircle.coe_sub]
  obtain ⟨z, hz⟩ := (mem_standardEuclideanLattice D _).mp
    (normalizedLatticePoint_sub_mem_of_mk_eq (euclideanSubspace U) b hb u x hu) i
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨z, by simpa only [zsmul_eq_mul, mul_one, PiLp.sub_apply] using hz⟩

theorem normalizedCoveredChart_projection {D Q : Type*} [Fintype D] [Fintype Q]
    (W : Submodule ℝ (EuclideanSpace ℝ D)) {n : ℕ} (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (bW : Basis Q ℤ (latticeSection (standardEuclideanLattice D) W))
    (d : ℕ) [NeZero d] (x : (W × (Fin n → ℤ)) × (Q → ZMod d)) :
    quotientIntegerCover (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d
      (normalizedCoveredChart W b hb bW d x) = normalizedLatticeQuotient W b hb x.1 := by
  let Γ := (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
  let e := coverKernelBasisEquiv Γ bW d (Nat.pos_of_ne_zero (NeZero.ne d))
  have hk : quotientIntegerCover Γ d (e x.2).val = 0 := (e x.2).property
  change quotientIntegerCover Γ d (normalizedCoverLift W b hb d x.1 + (e x.2).val) = _
  rw [map_add,
    normalizedCoverLift_projection W b hb d (Nat.pos_of_ne_zero (NeZero.ne d)), hk, add_zero]

namespace VectorPolynomial

variable {m : ℕ} {O J : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

omit [∀ j, Fintype (O j)] in
theorem coveredJetAmbientTorus_chart
    {I Q : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (Q j)] {n : Fin m → ℕ}
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (z : MixedCoveredJetSource I O Q n d) :
    coveredJetAmbientTorus U d (mixedCoveredJetChart U o b hb bW d z) =
      fun a => (mixedJetAmbientPoint U b o z.1 a : UnitAddCircle) := by
  funext a
  change subspaceAmbientTorus (U a.1) (euclideanSubspaceTorusEquiv (U a.1)
    (quotientIntegerCover _ d (normalizedCoveredChart _ (b a.1) (hb a.1) (bW a.1) d
      (mixedCoveredJetCoordinates U o d z a.1 a.2.1)))) a.2.2 = _
  rw [normalizedCoveredChart_projection]
  exact euclideanAmbientTorus_normalized (U a.1) (b a.1) (hb a.1) _ a.2.2

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedGridlessProfileBound
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "grid" => allocatedGridAxis (I := I) U b S.value

theorem exists_allocated_ambient_grid_factor
    (C : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (K : ℝ≥0) (D : ℕ)
    (hscale : ∀ a : {a // grid a}, allocatedGridAxisScale B U b S a ≤ K)
    (hD : ∀ a : {a // grid a}, Fintype.card (O a.val.1) ≤ D) :
    ∃ g : (JetAmbientIndex O J → UnitAddCircle) → ℝ,
      LipschitzWith ((Fintype.card {a // grid a} * (D * (2 * K ^ 2))) *
        (∑ j, C j * Fintype.card (J j))) g ∧
      (∀ z, g z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ w : JetAmbientIndex O J → ℝ, (∀ i, |w i| ≤ 1 / 4) →
        g (fun i => (w i : UnitAddCircle)) =
          allocatedNormalizedGridInterpolation B U b hR hσ S u rows
            (allocatedGridAmbientCoordinates B U b S o w) := by
  obtain ⟨hbound, hLip⟩ := allocatedNormalizedGridInterpolation_bounds
    B U b hR hσ S u rows K D hscale hD
  exact exists_real_quarter_torus_extension
    (fun w => allocatedNormalizedGridInterpolation B U b hR hσ S u rows
      (allocatedGridAmbientCoordinates B U b S o w)) _
    (hLip.comp (allocatedGridAmbientCoordinates_lipschitz B U b S o C hC))
    0 1 zero_le_one (fun w => hbound _)

theorem exists_allocated_ambient_grid_factor_uniform
    (C : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖) :
    let K : ℝ≥0 := (S.value : ℝ≥0) ^ (layerTailDegree m + 1)
    let D := Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
    ∃ g : (JetAmbientIndex O J → UnitAddCircle) → ℝ,
      LipschitzWith ((Fintype.card {a // grid a} * (D * (2 * K ^ 2))) *
        (∑ j, C j * Fintype.card (J j))) g ∧
      (∀ z, g z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ w : JetAmbientIndex O J → ℝ, (∀ i, |w i| ≤ 1 / 4) →
        g (fun i => (w i : UnitAddCircle)) =
          allocatedNormalizedGridInterpolation B U b hR hσ S u rows
            (allocatedGridAmbientCoordinates B U b S o w) := by
  intro K D
  apply exists_allocated_ambient_grid_factor B U b hR hσ S u rows o C hC K D
  · exact fun a => (allocatedGridAxisScale_bounds B U b S a).2
  · intro a
    apply Fintype.card_le_of_injective (fun t : O a.val.1 => (⟨a.val, t⟩ : Σ c : LayerSamplerAxis I n, O c.1))
    intro t w h
    exact eq_of_heq (Sigma.mk.inj h).2

theorem allocatedAmbientGridFactor_chart
    (g : (JetAmbientIndex O J → UnitAddCircle) → ℝ)
    (hvalue : ∀ w : JetAmbientIndex O J → ℝ, (∀ i, |w i| ≤ 1 / 4) →
      g (fun i => (w i : UnitAddCircle)) =
        allocatedNormalizedGridInterpolation B U b hR hσ S u rows
          (allocatedGridAmbientCoordinates B U b S o w))
    (x : G → IntegerScalarCubeBox α S.value)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U b S))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (z : MixedCoveredJetSource I O Q n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d (fun j _ => standardLatticeClosedQuarterBox (J j))) :
    g (coveredJetAmbientTorus U d (mixedCoveredJetChart U o b hb bW d z)) =
      allocatedGridJetDensity B U b hR hσ S x u v rows
        (fun a => coefficientJetAxisEquiv O I n z.1 a.val) := by
  rw [coveredJetAmbientTorus_chart U b hb o bW d z]
  have hsmall : ∀ a, |mixedJetAmbientPoint U b o z.1 a| ≤ 1 / 4 := by
    rintro ⟨j, t, i⟩
    exact (hz j (Set.mem_univ j) t (Set.mem_univ t)).1 i
  rw [hvalue _ hsmall, allocatedGridAmbientCoordinates_point,
    allocatedNormalizedGridInterpolation_grid B U b hR hσ S u rows x v]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedAmbientGrid
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "grid" => allocatedGridAxis (I := I) U b S.value

theorem exists_allocated_grid_mean_ambient_factor
    {A : Type*} [Fintype A] (p : FiniteProbabilityWeights A)
    (us : A → PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U b S))
    (C : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖) :
    let K : ℝ≥0 := (S.value : ℝ≥0) ^ (layerTailDegree m + 1)
    let D := Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
    ∃ g : (JetAmbientIndex O J → UnitAddCircle) → ℝ,
      LipschitzWith ((Fintype.card {a // grid a} * (D * (2 * K ^ 2))) *
        (∑ j, C j * Fintype.card (J j))) g ∧
      (∀ z, g z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U b S))
        (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
        {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
        (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        (d : ℕ) [NeZero d] (z : MixedCoveredJetSource I O Q n d),
        z ∈ mixedCoveredJetRegion U o b d (fun j _ => standardLatticeClosedQuarterBox (J j)) →
        g (coveredJetAmbientTorus U d (mixedCoveredJetChart U o b hb bW d z)) =
          p.mean (fun a => allocatedGridJetDensity B U b hR hσ S x (us a) v rows
            (fun a => coefficientJetAxisEquiv O I n z.1 a.val)) := by
  intro K D
  have hex (a : A) := exists_allocated_ambient_grid_factor_uniform
    B U b hR hσ S (us a) rows o C hC
  choose g hg hgb hgv using hex
  refine ⟨fun z => p.mean (fun a => g a z), p.mean_lipschitz_uniform _ hg, ?_, ?_⟩
  · intro z
    exact ⟨p.mean_nonneg (fun a => (hgb a z).1),
      (p.mean_mono (fun a => (hgb a z).2)).trans_eq (p.mean_const 1)⟩
  · intro x v hb Q _ bW d _ z hz
    unfold FiniteProbabilityWeights.mean
    apply Finset.sum_congr rfl
    intro a _
    exact congrArg (fun t : ℝ => p.weight a * t)
      (allocatedAmbientGridFactor_chart B U b hR hσ S (us a) rows o (g a) (hgv a) x v hb bW d z hz)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]
variable (hperiod : ∀ j, integerScalarLattice ((fun j : Fin m => {t : Finset α // t ∈ rowSets j}) j) (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) ((fun j => (Subtype.val : rowSets j → Finset α)) j)).mulVecLin.range)

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "quarter" => (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter
local notation "gridDensity" => allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x

include v₀ in
theorem exists_allocated_supported_sliced_ambient_grid_s2_oai
    (C : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖) :
    let K : ℝ≥0 := (S.value : ℝ≥0) ^ (layerTailDegree m + 1)
    let D := Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)
    ∃ g : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℝ,
      LipschitzWith ((Fintype.card gridAxes * (D * (2 * K ^ 2))) *
        (∑ j, C j * Fintype.card (J j))) g ∧
      (∀ z, g z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ z : MixedCoveredJetSource I rowTypes Q n d, z ∈ region →
        g (coveredJetAmbientTorus U d (chart z)) =
          gridDensity ((coefficientJetAxisSplit rowTypes I n grid z.1).1) := by
  classical
  intro K D
  obtain ⟨g, hg, hgb, hgv⟩ := exists_allocated_grid_mean_ambient_factor
    B U b hR hσ S rows o gridLaw id C hC
  refine ⟨g, hg, hgb, ?_⟩
  intro z hz
  exact (hgv x v₀ hb bW d z hz).trans
    (allocatedSupportedSlicedFullGridDensity_mean_s2 B U b hR hσ S rowSets H step c hH hsubset q r hcell
      x v₀ _)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uα, u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocated_supported_sliced_ambient_grid_s2_oai.{uα, u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.exists_allocated_supported_sliced_ambient_grid_s2_oai.{uα, u_1, u_2, u_3, u_4, u_5}
