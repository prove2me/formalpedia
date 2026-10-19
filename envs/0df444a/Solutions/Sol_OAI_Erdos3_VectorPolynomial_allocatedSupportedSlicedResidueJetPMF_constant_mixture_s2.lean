-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:45:01.275142+00:00
-- url     : https://prove2.me/submissions/8acde5d0-88cc-4f51-add5-945ad3b30951

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal
namespace OAI

section

namespace Erdos3

open VectorPolynomial

theorem principalCoefficientChoice_injective {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (hd : 0 < h d) :
    Function.Injective (principalCoefficientChoice (G := G) (B := B) h d) := by
  intro x y hxy
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some b =>
      exact False.elim (canonicalPrincipalExponent_ne_zero h d hd b
        (congrArg Subtype.val hxy).symm)
  | some b =>
    cases y with
    | none =>
      exact False.elim (canonicalPrincipalExponent_ne_zero h d hd b
        (congrArg Subtype.val hxy))
    | some b' =>
      exact congrArg some (principalCoefficientSlot_injective h d hd hxy)

theorem principalCoefficientMarginal {D G : Type*} [Fintype D] [Fintype G]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (d : D) (hd : 0 < h d)
    (p : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → PMF ℤ) :
    (independentProductPMF p).map (fun a r => a (principalCoefficientChoice h d r)) =
      independentProductPMF (fun r => p (principalCoefficientChoice h d r)) :=
  independentProductPMF_marginal p _ (principalCoefficientChoice_injective h d hd)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentPMFOption
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem independentProductPMF_option {B X : Type*} [Fintype B]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : Option B → PMF X) :
    independentProductPMF p = (p none).bind (fun c =>
      (independentProductPMF (fun b => p (some b))).map
        (fun x q => q.elim c x)) := by
  ext z
  have hz : (fun q : Option B => q.elim (z none) (fun b => z (some b))) = z := by
    funext q
    cases q <;> rfl
  have hinj (c : X) : Function.Injective (fun (x : B → X) (q : Option B) => q.elim c x) := by
    intro x y h
    funext b
    exact congrFun h (some b)
  rw [PMF.bind_apply, tsum_eq_single (z none)]
  · have hm := pmf_map_injective_at (independentProductPMF (fun b => p (some b)))
      (fun (x : B → X) (q : Option B) => q.elim (z none) x) (hinj (z none))
      (fun b => z (some b))
    rw [hz] at hm
    rw [hm]
    simp only [independentProductPMF_apply, Fintype.prod_option]
  · intro c hc
    have hr : z ∉ Set.range (fun (x : B → X) (q : Option B) => q.elim c x) := by
      rintro ⟨x, he⟩
      exact hc (congrFun he none)
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

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

theorem allocatedPhysicalGridJetPMF_principal
    (hmoderate : basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1))
    {α O : Type*} [Fintype α] [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (rows : O → Finset α) :
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1) rows)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i) =
      (independentProductPMF (fun r : Option (B ⟨j, Sum.inr i⟩) =>
        allocatedLayerIntegerPMFs B U basis hR hσ S j i
          (principalCoefficientChoice (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ r))).map
        (fun c o => booleanCoefficient (fun _ => c none) (rows o) +
          ∑ b : B ⟨j, Sum.inr i⟩, c (some b) *
            integerBooleanBlockJet (fun v r => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ r : ℤ)) (rows o)) := by
  rw [allocatedPhysicalGridJetPMF_blocks B U basis hR hσ S j i hmoderate x y rows]
  rw [← principalCoefficientMarginal (G := G) (B := B) (layerSamplerDegree I n)
    ⟨j, Sum.inr i⟩ (Nat.zero_lt_succ _) (allocatedLayerIntegerPMFs B U basis hR hσ S j i)]
  rw [PMF.map_comp]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidueJet
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

theorem allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2_oai
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value) :
    (conditioned).toPMF.bind (fun y =>
      integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
        (fun t : rows => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i)) =
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i
        (principalCoefficientChoice (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ none)).bind
        (fun z => allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows
          (fun t => booleanCoefficient (fun _ : Finset α => z) t)) := by
  let p := (conditioned).toPMF
  let a := dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
    allocatedLayerIntegerPMFs B U basis hR hσ S j i
      (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))
  let constLaw := allocatedLayerIntegerPMFs B U basis hR hσ S j i
    (principalCoefficientChoice (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ none)
  let f (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
      (z : ℤ) (coeff : B ⟨j, Sum.inr i⟩ → ℤ) : rows → ℤ :=
    (fun t : rows => booleanCoefficient (fun _ : Finset α => z) t) +
      ∑ b, fun t : rows => coeff b * integerBooleanBlockJet
        (fun v k => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ k : ℤ)) t
  have hpoint y : integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
        (fun t : rows => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i) =
      constLaw.bind (fun z => a.map (f y z)) := by
    rw [allocatedPhysicalGridJetPMF_principal B U basis hR hσ S j i hgrid,
      independentProductPMF_option, PMF.map_bind]
    simp only [PMF.map_comp]
    apply congrArg (fun k : ℤ → PMF (rows → ℤ) => constLaw.bind k)
    funext z
    apply congrArg (fun g : (B ⟨j, Sum.inr i⟩ → ℤ) → rows → ℤ => a.map g)
    funext coeff t
    simp only [Function.comp_apply, f, Pi.add_apply, Finset.sum_apply,
      Option.elim_none, Option.elim_some]
  simp_rw [hpoint]
  change p.bind (fun y => constLaw.bind (fun z => a.map (f y z))) =
    constLaw.bind (fun z => a.bind (fun coeff => p.map (fun y => f y z coeff)))
  refine (PMF.bind_comm p constLaw (fun y z => a.map (f y z))).trans ?_
  apply congrArg (fun k : ℤ → PMF (rows → ℤ) => constLaw.bind k)
  funext z
  exact PMF.bind_comm p a (fun y coeff => PMF.pure (f y z coeff))

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2_oai.{u_1, u_2, u_3, u_4, u_5}
