-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedSlicedPhysicalResidueMean_eq_rationalMean_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:40:49.481978+00:00
-- url     : https://prove2.me/submissions/d7615326-f33f-48b3-92b7-097d26f4066f

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B244
import Definitions.Def_OAIE3v2B247

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialResidues
namespace OAI

section

namespace Erdos3

theorem integerPolynomial_eval_residue {X : Type*} (p : MvPolynomial X ℤ)
    (m : ℕ) (x : X → ℤ) :
    ((MvPolynomial.eval x p : ℤ) : ZMod m) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod m)) (integerResidueMap X m x) p := by
  have heq : integerResidueMap X m x = (fun i => (x i : ZMod m)) := rfl
  rw [heq]
  simpa only [MvPolynomial.eval₂_id, RingHom.comp_id, Int.coe_castRingHom] using
    MvPolynomial.hom_eval₂ p (RingHom.id ℤ) (Int.castRingHom (ZMod m)) x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialImage
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {L Tag V : Type*} [Fintype L]

theorem crtInput_reduce (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (x : ∀ l : L, V → ZMod (q l)) (l : L) (v : V) :
    ZMod.castHom (Finset.dvd_prod_of_mem q (Finset.mem_univ l)) (ZMod (q l))
      (crtInput q hq x v) = x l v := by
  rw [← ZMod.prodEquivPi_apply q hq]
  exact congrFun ((ZMod.prodEquivPi q hq).apply_symm_apply (fun l => x l v)) l

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformResidueSmallPeriod
namespace OAI


namespace Erdos3

open scoped BigOperators Classical Matrix

theorem uniformPMF_map_fiber {G H : Type*} [Fintype G] [Nonempty G]
    [DecidableEq H] (f : G → H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card G := by
  classical
  rw [pmf_map_toReal_indicator, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

theorem uniformPMF_map_hom_image {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      if y ∈ f.range then (Nat.card f.range : ℝ)⁻¹ else 0 := by
  classical
  rw [uniformPMF_map_fiber]
  by_cases hy : y ∈ f.range
  · simp only [hy, ite_true]
    have he := AddMonoidHom.card_fiber_eq_of_mem_range f hy
      (show (0 : H) ∈ Set.range f from ⟨0, f.map_zero⟩)
    have hk : (Finset.univ.filter (fun x => f x = 0)).card = Fintype.card f.ker := by
      simp [Fintype.card_subtype, AddMonoidHom.mem_ker]
    have hc : Fintype.card f.ker * Fintype.card f.range = Fintype.card G := by
      simpa only [AddSubgroup.index_ker, Nat.card_eq_fintype_card] using f.ker.card_mul_index
    rw [he, hk, ← hc, Nat.cast_mul, Nat.card_eq_fintype_card]
    have hkn : (Fintype.card f.ker : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  · simp only [hy, ite_false]
    have hz : Finset.univ.filter (fun x => f x = y) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hy ⟨x, (Finset.mem_filter.mp hx).2⟩
    simp [hz]

theorem uniformPMF_map_hom_index {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      (if y ∈ f.range then (f.range.index : ℝ) else 0) / Fintype.card H := by
  classical
  rw [uniformPMF_map_hom_image]
  by_cases hy : y ∈ f.range
  · simp only [hy, ite_true]
    have hcard : (Nat.card f.range : ℝ) * f.range.index = Fintype.card H := by
      have h := f.range.card_mul_index
      rw [Nat.card_eq_fintype_card (α := H)] at h
      exact_mod_cast h
    have hn : (Nat.card f.range : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have hh : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    apply (eq_div_iff hh).mpr
    rw [← hcard, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · simp [hy]

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformHomFiberWeights
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem uniform_mean_surjective_hom_fiber {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (y : H) :
    (FiniteProbabilityWeights.uniform G).mean (fun x => if f x = y then (1 : ℝ) else 0) =
      (Fintype.card H : ℝ)⁻¹ := by
  have h := uniformPMF_map_hom_index f y
  have hr : f.range = ⊤ := by
    ext z
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_top, iff_true]
    exact hf z
  have hy : y ∈ f.range := hf y
  rw [if_pos hy, hr] at h
  simp only [AddSubgroup.index_top, Nat.cast_one, one_div] at h
  rw [uniformPMF_map_fiber] at h
  calc
    _ = ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card G := by
      rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card]
      simp
    _ = _ := h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

theorem pi_uniform_weight {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, Nonempty (Ω j)]
    (x : ∀ j, Ω j) :
    (pi (fun j => uniform (Ω j))).weight x = (uniform (∀ j, Ω j)).weight x := by
  simp [pi, uniform, Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

end Erdos3.FiniteProbabilityWeights

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalForecastGridTail
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem rationalOutputDensity_test {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ) (N : ℕ) [NeZero N]
    (test : (J → ZMod N) → ℂ) :
    (𝔼 b, (rationalOutputDensity p Y N b : ℂ) * test b) =
      p.complexMean (fun x => test (fun j => (Y x j : ZMod N))) := by
  let F := fun x j => (Y x j : ZMod N)
  have hmass (b) : finiteImageMass p F b = (p.fiberLaw F).weight b := by
    unfold finiteImageMass FiniteProbabilityWeights.fiberLaw FiniteProbabilityWeights.fiberMean
    congr 1
    funext x
    split_ifs <;> rfl
  have hcard : (Fintype.card (J → ZMod N) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [Fintype.expect_eq_sum_div_card]
  simp only [rationalOutputDensity, Complex.ofReal_mul, Complex.ofReal_natCast,
    mul_assoc, ← Finset.mul_sum]
  rw [mul_div_cancel_left₀ _ hcard]
  change (∑ b, (finiteImageMass p F b : ℂ) * test b) = _
  simp_rw [hmass]
  exact p.fiberLaw_complexMean F test

theorem rationalOutputDensity_divisor_test {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ)
    {q N : ℕ} [NeZero N] [NeZero q] (hq : q ∣ N)
    (test : (J → ZMod q) → ℂ) :
    (𝔼 b : J → ZMod N, (rationalOutputDensity p Y N b : ℂ) *
      test (fun j => ZMod.castHom hq (ZMod q) (b j))) =
      p.complexMean (fun x => test (fun j => (Y x j : ZMod q))) := by
  simpa only [map_intCast] using rationalOutputDensity_test p Y N
    (fun b => test (fun j => ZMod.castHom hq (ZMod q) (b j)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RationalPolynomialForecastBoxError
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem tupleResidueReduction_surjective {A : Type*} {q N : ℕ} (hq : q ∣ N) :
    Function.Surjective (tupleResidueReduction (A := A) hq) := by
  intro y
  choose x hx using fun a => ZMod.castHom_surjective hq (y a)
  exact ⟨x, funext hx⟩

theorem integerLongPolynomialOutput_reduce {A I J : Type*}
    (poly : J → MvPolynomial (A ⊕ I) ℤ) (inactive : I → ℤ)
    {q N : ℕ} [NeZero N] (hq : q ∣ N) (t : A → ZMod N) :
    (fun j => (integerLongPolynomialOutput poly inactive N t j : ZMod q)) =
      fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (Sum.elim (tupleResidueReduction hq t) (fun i => (inactive i : ZMod q))) (poly j) := by
  funext j
  rw [integerLongPolynomialOutput, integerPolynomial_eval_residue]
  congr 1
  funext v
  cases v with
  | inl a =>
    change (((t a).val : ℤ) : ZMod q) = ZMod.castHom hq (ZMod q) (t a)
    have h := congrArg (ZMod.castHom hq (ZMod q)) (ZMod.natCast_zmod_val (t a))
    simpa only [map_natCast, Int.cast_natCast] using h
  | inr i => rfl

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

include hR hσ in
theorem allocatedOriginalSampleInactiveCoefficients_supported
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j)) :
    ∀ a d, allocatedOriginalSampleInactiveCoefficients B selected sample a d ∈
      (allocatedLayerIntegerPMFs B U b hR hσ S (selected a).1 (selected a).2 d).support := by
  intro a d
  exact ((mixedArraySupported_iff_rows _ _ _ (sample (selected a).1)).mp
    (hs (selected a).1)).2 (selected a).2 d

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MixedSmoothUniformBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem uniform_fiberLaw_surjective_hom {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) :
    (FiniteProbabilityWeights.uniform G).fiberLaw f =
      FiniteProbabilityWeights.uniform H := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro y
  have hh := uniform_mean_surjective_hom_fiber f hf y
  change _ = (Fintype.card H : ℝ)⁻¹
  convert hh using 1
  unfold FiniteProbabilityWeights.fiberLaw FiniteProbabilityWeights.fiberMean
  congr 1

theorem uniform_tupleResidueReduction_fiberLaw {D : Type*}
    [Fintype D] [DecidableEq D] {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) :
    (FiniteProbabilityWeights.uniform (D → ZMod N)).fiberLaw (tupleResidueReduction hMN) =
      FiniteProbabilityWeights.uniform (D → ZMod M) :=
  uniform_fiberLaw_surjective_hom (tupleResidueReduction hMN)
    (tupleResidueReduction_surjective hMN)

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem FiniteProbabilityWeights.fiberLaw_comp {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (p : FiniteProbabilityWeights X) (f : X → Y) (g : Y → Z) :
    (p.fiberLaw f).fiberLaw g = p.fiberLaw (g ∘ f) := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro z
  change (p.fiberLaw f).mean (fun y => if g y = z then (1 : ℝ) else 0) =
    p.mean (fun x => if g (f x) = z then (1 : ℝ) else 0)
  exact p.fiberLaw_mean f _

theorem uniform_tupleResidueReduction_fiberLaw_postcompose {D Y : Type*}
    [Fintype D] [DecidableEq D] [Fintype Y]
    {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (f : (D → ZMod M) → Y) :
    (FiniteProbabilityWeights.uniform (D → ZMod N)).fiberLaw
        (fun x => f (tupleResidueReduction hMN x)) =
      (FiniteProbabilityWeights.uniform (D → ZMod M)).fiberLaw f := by
  rw [← uniform_tupleResidueReduction_fiberLaw hMN,
    FiniteProbabilityWeights.fiberLaw_comp]
  rfl

theorem tupleResidueReduction_affine {D : Type*} {M N : ℕ}
    (hMN : M ∣ N) (a x : D → ZMod N) (step : ℕ) :
    tupleResidueReduction hMN (fun d => a d + (step : ZMod N) * x d) =
      fun d => tupleResidueReduction hMN a d +
        (step : ZMod M) * tupleResidueReduction hMN x d := by
  funext d
  change ZMod.castHom hMN (ZMod M) (a d + (step : ZMod N) * x d) = _
  simp only [map_add, map_mul, map_natCast]
  rfl

theorem uniform_affine_tupleResidueReduction_fiberLaw {D : Type*}
    [Fintype D] [DecidableEq D] {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (a : D → ZMod N) (step : ℕ) :
    ((FiniteProbabilityWeights.uniform (D → ZMod N)).fiberLaw
        (fun x d => a d + (step : ZMod N) * x d)).fiberLaw
          (tupleResidueReduction hMN) =
      (FiniteProbabilityWeights.uniform (D → ZMod M)).fiberLaw
        (fun y d => tupleResidueReduction hMN a d + (step : ZMod M) * y d) := by
  rw [FiniteProbabilityWeights.fiberLaw_comp]
  simp only [Function.comp_def, tupleResidueReduction_affine]
  exact uniform_tupleResidueReduction_fiberLaw_postcompose (D := D) hMN
    (fun y d => tupleResidueReduction hMN a d + (step : ZMod M) * y d)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialInputAffineLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

theorem crtPrimePowerPolynomialLaw_eq_uniform (p A : L → ℕ) [∀ l, NeZero (p l)] :
    crtPrimePowerPolynomialLaw (V := V) p A =
      FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l)) := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro x
  exact FiniteProbabilityWeights.pi_uniform_weight x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialInputStepLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem padicStepQuotientUnit_factor (p A step : ℕ)
    (hp : p.Prime) (hstep : step ≠ 0) :
    (p : ZMod (p ^ A)) ^ padicValNat p step *
        padicStepQuotientUnit p A step hp hstep = (step : ZMod (p ^ A)) := by
  rw [padicStepQuotientUnit_coe, ← Nat.cast_pow, ← Nat.cast_mul,
    Nat.mul_div_cancel' (pow_padicValNat_dvd (p := p) (n := step))]

variable {L V : Type*} [Fintype L]

omit [Fintype L] in
theorem prescribedCRTArbitraryStepEquiv_local_step (p A : L → ℕ) (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0)
    (x : ∀ l, V → ZMod (p l ^ A l)) (l : L) (v : V) :
    (p l : ZMod (p l ^ A l)) ^ padicValNat (p l) step *
        prescribedCRTArbitraryStepEquiv p A step hp hstep x l v =
      (step : ZMod (p l ^ A l)) * x l v := by
  change (p l : ZMod (p l ^ A l)) ^ padicValNat (p l) step *
    ((padicStepQuotientUnit (p l) (A l) step (hp l) hstep : ZMod (p l ^ A l)) *
      x l v) = _
  rw [← mul_assoc, padicStepQuotientUnit_factor]

theorem prescribedCRTPolynomialInput_arbitrary_step (p A : L → ℕ) (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin x : ∀ l, V → ZMod (p l ^ A l)) (v : V) :
    prescribedCRTPolynomialInput p A (fun l => padicValNat (p l) step) hq origin
        (prescribedCRTArbitraryStepEquiv p A step hp hstep x) v =
      crtInput (fun l => p l ^ A l) hq origin v +
        (step : ℕ) * crtInput (fun l => p l ^ A l) hq x v := by
  apply (ZMod.prodEquivPi (fun l => p l ^ A l) hq).injective
  funext l
  rw [ZMod.prodEquivPi_apply, ZMod.prodEquivPi_apply]
  simp only [prescribedCRTPolynomialInput, map_add, map_mul, map_natCast]
  rw [crtInput_reduce (fun l => p l ^ A l) hq _ l v,
    crtInput_reduce (fun l => p l ^ A l) hq origin l v,
    crtInput_reduce (fun l => p l ^ A l) hq x l v]
  exact congrArg (origin l v + ·)
    (prescribedCRTArbitraryStepEquiv_local_step p A step hp hstep x l v)

attribute [local instance] OAI.Erdos3.arbitraryStepCRTModulusNeZero
variable [Fintype V]

theorem crtPolynomialInputLaw_arbitrary_step_uniform
    (p A : L → ℕ) [∀ l, NeZero (p l)] (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l)) :
    crtPolynomialInputLaw p A (fun l => padicValNat (p l) step) hq origin =
      (FiniteProbabilityWeights.uniform (V → ZMod (∏ l, p l ^ A l))).fiberLaw
        (fun x v => crtInput (fun l => p l ^ A l) hq origin v + (step : ℕ) * x v) := by
  let E := crtInputAddEquiv (V := V) (fun l => p l ^ A l) hq
  let T := prescribedCRTArbitraryStepEquiv (V := V) p A step hp hstep
  let f : (V → ZMod (∏ l, p l ^ A l)) → (V → ZMod (∏ l, p l ^ A l)) :=
    fun x v => crtInput (fun l => p l ^ A l) hq origin v + (step : ℕ) * x v
  have hT := uniform_fiberLaw_surjective_hom T.toAddMonoidHom T.surjective
  change (FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l))).fiberLaw T = _ at hT
  have hE := uniform_fiberLaw_surjective_hom E.toAddMonoidHom E.surjective
  change (FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l))).fiberLaw E = _ at hE
  have heq : prescribedCRTPolynomialInput p A (fun l => padicValNat (p l) step) hq origin ∘ T =
      f ∘ E := by
    funext x v
    exact prescribedCRTPolynomialInput_arbitrary_step p A step hp hstep hq origin x v
  rw [crtPolynomialInputLaw, crtPrimePowerPolynomialLaw_eq_uniform]
  calc
    _ = ((FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l))).fiberLaw T).fiberLaw
        (prescribedCRTPolynomialInput p A (fun l => padicValNat (p l) step) hq origin) := by rw [hT]
    _ = (FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l))).fiberLaw (f ∘ E) := by
      rw [FiniteProbabilityWeights.fiberLaw_comp, heq]
    _ = _ := by rw [← FiniteProbabilityWeights.fiberLaw_comp, hE]

omit [Fintype V] in
theorem crtInput_intCast_apply (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k))) (c : V → ℤ) (v : V) :
    crtInput q hq (fun l v => (c v : ZMod (q l))) v =
      (c v : ZMod (∏ l, q l)) := by
  exact map_intCast (ZMod.prodEquivPi q hq).symm (c v)

theorem crtPolynomialInputLaw_arbitrary_step_divisor_affine
    (p A : L → ℕ) [∀ l, NeZero (p l)] (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (c : V → ℤ) {q : ℕ} [NeZero q] (hdiv : q ∣ ∏ l, p l ^ A l) :
    (crtPolynomialInputLaw p A (fun l => padicValNat (p l) step) hq
      (fun l v => (c v : ZMod (p l ^ A l)))).fiberLaw (tupleResidueReduction hdiv) =
      (FiniteProbabilityWeights.uniform (V → ZMod q)).fiberLaw
        (fun x v => (c v : ZMod q) + (step : ZMod q) * x v) := by
  rw [crtPolynomialInputLaw_arbitrary_step_uniform p A step hp hstep hq,
    uniform_affine_tupleResidueReduction_fiberLaw hdiv]
  congr 1
  funext x v
  change ZMod.castHom hdiv (ZMod q)
    (crtInput (fun l => p l ^ A l) hq (fun l v => (c v : ZMod (p l ^ A l))) v) + _ = _
  rw [crtInput_intCast_apply, map_intCast]

theorem crtPolynomialInputLaw_arbitrary_step_divisor_complexMean
    (p A : L → ℕ) [∀ l, NeZero (p l)] (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (c : V → ℤ) {q : ℕ} [NeZero q] (hdiv : q ∣ ∏ l, p l ^ A l)
    (f : (V → ZMod q) → ℂ) :
    (crtPolynomialInputLaw p A (fun l => padicValNat (p l) step) hq
      (fun l v => (c v : ZMod (p l ^ A l)))).complexMean
        (fun x => f (tupleResidueReduction hdiv x)) =
      (FiniteProbabilityWeights.uniform (V → ZMod q)).complexMean
        (fun x => f (fun v => (c v : ZMod q) + (step : ZMod q) * x v)) := by
  rw [← FiniteProbabilityWeights.fiberLaw_complexMean,
    crtPolynomialInputLaw_arbitrary_step_divisor_affine p A step hp hstep hq c hdiv,
    FiniteProbabilityWeights.fiberLaw_complexMean]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTsum
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X R : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem fiberMean_eq_zero_of_not_mem_image (F : X → R) (f : X → ℝ)
    (r : R) (hr : r ∉ Finset.univ.image F) : p.fiberMean F r f = 0 := by
  have hne : ∀ x, F x ≠ r := by
    intro x hx
    exact hr (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩)
  simp only [fiberMean, hne, ite_false, mean_const]

theorem complexMean_fiber_factor_sum_image (F : X → R) (f : X → ℝ) (a : R → ℂ) :
    p.complexMean (fun x => (f x : ℂ) * a (F x)) =
      ∑ r ∈ Finset.univ.image F, (p.fiberMean F r f : ℂ) * a r := by
  unfold complexMean fiberMean mean
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have hx : F x ∈ Finset.univ.image F := Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  have he (r : R) : ((if F x = r then f x else 0 : ℝ) : ℂ) =
      if F x = r then (f x : ℂ) else 0 := by split_ifs <;> rfl
  simp [he, mul_ite, ite_mul, mul_assoc, hx]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedPeriodicGridQuadrature
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem rationalInactiveForecast_zero_off_image {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    (gridVolume : ℝ) (z : Z) (hz : z ∉ Finset.univ.image gridPoint) (b : J → ZMod N) :
    rationalInactiveForecast inactive active gridPoint Y N gridVolume z b = 0 := by
  rw [rationalInactiveForecast,
    inactive.fiberMean_eq_zero_of_not_mem_image gridPoint _ z hz, mul_zero]

theorem rationalInactiveForecast_divisor_tsum_test {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ)
    {q N : ℕ} [NeZero N] [NeZero q] (hq : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (test : Z → (J → ZMod q) → ℂ) :
    (∑' z, 𝔼 b : J → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b / gridVolume : ℝ) : ℂ) *
        test z (fun j => ZMod.castHom hq (ZMod q) (b j))) =
      inactive.complexMean (fun i => (active i).complexMean
        (fun a => test (gridPoint i) (fun j => (Y i a j : ZMod q)))) := by
  classical
  rw [tsum_eq_sum (s := Finset.univ.image gridPoint) (fun z hz => by
    simp only [rationalInactiveForecast_zero_off_image inactive active gridPoint Y N gridVolume z hz,
      zero_div, Complex.ofReal_zero, zero_mul, Finset.expect_const_zero])]
  simp only [rationalInactiveForecast, mul_div_cancel_left₀ _ hV]
  rw [← Finset.expect_sum_comm]
  have hswap (b : J → ZMod N) :
      (∑ z ∈ Finset.univ.image gridPoint,
        (inactive.fiberMean gridPoint z (fun i => rationalOutputDensity (active i) (Y i) N b) : ℂ) *
          test z (fun j => ZMod.castHom hq (ZMod q) (b j))) =
      inactive.complexMean (fun i => (rationalOutputDensity (active i) (Y i) N b : ℂ) *
        test (gridPoint i) (fun j => ZMod.castHom hq (ZMod q) (b j))) :=
    (inactive.complexMean_fiber_factor_sum_image gridPoint _ _).symm
  simp_rw [hswap]
  unfold FiniteProbabilityWeights.complexMean
  rw [Finset.expect_sum_comm]
  simp_rw [← Finset.mul_expect]
  apply Finset.sum_congr rfl
  intro i _
  rw [rationalOutputDensity_divisor_test (active i) (Y i) hq]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedForecastShortRawDependence
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem samplerSeparated_eval₂_raw_congr
    {D G R : Type*} {B : D → Type*} [CommRing R]
    (inactive : D → Prop) (h : D → ℕ)
    (poly : MvPolynomial (SamplerTupleIndex G B h) ℤ)
    (long : SamplerLongVariables inactive G B h → R)
    (v w : PrincipalTupleIndex B h × Option Empty → R)
    (hvw : ∀ j : PrincipalTupleIndex B h, inactive j.1 → v (j, none) = w (j, none)) :
    MvPolynomial.eval₂ (Int.castRingHom R) (Sum.elim long v)
        (rename (samplerSeparatedVariable inactive h) poly) =
      MvPolynomial.eval₂ (Int.castRingHom R) (Sum.elim long w)
        (rename (samplerSeparatedVariable inactive h) poly) := by
  simp only [eval₂_rename]
  congr 1
  funext k
  cases k with
  | inl g => rfl
  | inr j =>
    by_cases hj : inactive j.1
    · simpa only [Function.comp_apply, samplerSeparatedVariable_inactive inactive h _ _ _ hj,
        Sum.elim_inr] using hvw j hj
    · simp only [Function.comp_apply, samplerSeparatedVariable_active inactive h _ _ _ hj,
        Sum.elim_inl]

namespace VectorPolynomial

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

omit [Fintype X] [∀ j, Fintype (E j)] in
theorem allocatedForecastPolynomial_eval₂_raw_congr
    (inactive : LayerSamplerAxis I n → Prop)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    {R : Type*} [CommRing R]
    (long : LayerSamplerLongVariables inactive G B → R)
    (v w : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → R)
    (hvw : ∀ j : PrincipalTupleIndex B (layerSamplerDegree I n),
      inactive j.1 → v (j, none) = w (j, none))
    (o : Sigma (AllocatedCongruenceRankOutput X E inactive)) :
    MvPolynomial.eval₂ (Int.castRingHom R) (Sum.elim long v)
        (allocatedForecastPolynomial inactive base noise deck projection o) =
      MvPolynomial.eval₂ (Int.castRingHom R) (Sum.elim long w)
        (allocatedForecastPolynomial inactive base noise deck projection o) :=
  samplerSeparated_eval₂_raw_congr inactive (layerSamplerDegree I n)
    (allocatedUnconditionedCongruenceIntegerPolynomial inactive o.1 base noise deck
      (projection o.1) o.2) long v w hvw

variable (B) {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "sides" => allocatedPrincipalSides B U basis S

omit [Fintype X] [∀ j, Fintype (E j)] in
theorem allocatedShortPrincipalRaw_restrict
    (v : PrincipalIntegerTuples B degree Empty sides)
    (j : PrincipalTupleIndex B degree) (hj : short j.1) :
    allocatedShortPrincipalRaw B U basis S (principalAxisRestrict short v) (j, none) =
      (v j none : ℤ) := by
  simp only [allocatedShortPrincipalRaw, hj, dite_true, principalAxisRestrict]

omit [Fintype X] [∀ j, Fintype (E j)] in
theorem allocatedForecastPolynomial_short_raw
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (q : ℕ) (long : LayerSamplerLongVariables short G B → ZMod q)
    (v : PrincipalIntegerTuples B degree Empty sides)
    (o : Sigma (AllocatedCongruenceRankOutput X E short)) :
    MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (Sum.elim long (fun k => ((v k.1 k.2 : ℤ) : ZMod q)))
        (allocatedForecastPolynomial short base noise deck projection o) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (Sum.elim long (fun k => (allocatedShortPrincipalRaw B U basis S
          (principalAxisRestrict short v) k : ZMod q)))
        (allocatedForecastPolynomial short base noise deck projection o) := by
  apply allocatedForecastPolynomial_eval₂_raw_congr
  intro j hj
  rw [allocatedShortPrincipalRaw_restrict B U basis S v j hj]

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativeJointTestBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*}

theorem forecastInactiveFixedOutput_congr_selected
    (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x x' : G → IntegerScalarCubeBox Empty S.value)
    (y y' : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U basis S))
    (hy : ∀ a (b : B ⟨(selected a).1, Sum.inr (selected a).2⟩)
      (v : Fin ((selected a).1.val + 1)) (o : Option Empty),
      y ⟨⟨(selected a).1, Sum.inr (selected a).2⟩, b, v⟩ o =
        y' ⟨⟨(selected a).1, Sum.inr (selected a).2⟩, b, v⟩ o) :
    forecastInactiveFixedOutput B U basis S selected c x y =
      forecastInactiveFixedOutput B U basis S selected c x' y' := by
  funext a row
  have hmoderate := (hsmall a).trans (Nat.pow_le_pow_right S.positive
    ((layerDegree_le_tailDegree (selected a).1).trans (Nat.le_succ _)))
  unfold forecastInactiveFixedOutput
  rw [allocatedPhysicalGridJet_blocks B U basis hR hσ S (selected a).1 (selected a).2
    hmoderate (c a) (hc a) x y,
    allocatedPhysicalGridJet_blocks B U basis hR hσ S (selected a).1 (selected a).2
      hmoderate (c a) (hc a) x' y']
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  apply congrArg (fun f => integerBooleanBlockJet f (row : Finset Empty))
  funext v o
  exact congrArg Subtype.val (hy a b v o)

theorem forecastInactiveFixedOutput_congr_restrict
    (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (P : LayerSamplerAxis I n → Prop)
    (hselected : ∀ a, P ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (x x' : G → IntegerScalarCubeBox Empty S.value)
    (y y' : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U basis S))
    (hy : principalAxisRestrict P y = principalAxisRestrict P y') :
    forecastInactiveFixedOutput B U basis S selected c x y =
      forecastInactiveFixedOutput B U basis S selected c x' y' := by
  apply forecastInactiveFixedOutput_congr_selected B U basis S hR hσ
    selected hsmall c hc x x' y y'
  intro a b v o
  exact congrFun (congrFun hy ⟨⟨_, hselected a⟩, b, v⟩) o

theorem forecastInactiveFixedOutput_congr_short_restrict
    (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x x' : G → IntegerScalarCubeBox Empty S.value)
    (y y' : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U basis S))
    (hy : principalAxisRestrict (allocatedShortAxis U basis S.value) y =
      principalAxisRestrict (allocatedShortAxis U basis S.value) y') :
    forecastInactiveFixedOutput B U basis S selected c x y =
      forecastInactiveFixedOutput B U basis S selected c x' y' :=
  forecastInactiveFixedOutput_congr_restrict B U basis S hR hσ selected hsmall c hc
    (allocatedShortAxis U basis S.value) hsmall x x' y y' hy

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {A : Type*}

theorem forecastInactiveFixedOutput_eq_shortGrid
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U basis S)) :
    forecastInactiveFixedOutput B U basis S selected c x y =
      forecastInactiveShortGrid B U basis S selected c
        (principalAxisRestrict (allocatedShortAxis U basis S.value) y) := by
  unfold forecastInactiveShortGrid
  apply forecastInactiveFixedOutput_congr_short_restrict B U basis S hR hσ
    selected hsmall c hc
  exact (principalAxisRestrict_join_left (allocatedShortAxis U basis S.value) _ _).symm

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineFixedPathRationalReference
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {L V Short Out : Type*} [Fintype L] [Fintype V]
  [Fintype Out] [DecidableEq Out]

attribute [local instance] OAI.Erdos3.arbitraryStepForecastModulusNeZero
theorem rationalInactivePolynomialForecast_arbitraryStepCRT_tsum_marginal
    {I Z : Type*} [Fintype I]
    (inactive : FiniteProbabilityWeights I) (gridPoint : I → Z)
    (p e : L → ℕ) [∀ l, NeZero (p l)] (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0)
    (hcoprime : Pairwise (fun l k => (p l ^ e l).Coprime (p k ^ e k)))
    (cLong : V → ℤ)
    (poly : Out → MvPolynomial (V ⊕ Short) ℤ) (inactiveCoord : I → Short → ℤ)
    {q : ℕ} [NeZero q] (hdiv : q ∣ ∏ l, p l ^ e l)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (test : Z → (Out → ZMod q) → ℂ) :
    (∑' z, 𝔼 b : Out → ZMod (∏ l, p l ^ e l),
      ((rationalInactiveForecast inactive
        (fun _ => crtPolynomialInputLaw p e (fun l => padicValNat (p l) step) hcoprime
          (fun l v => (cLong v : ZMod (p l ^ e l)))) gridPoint
        (fun i => integerLongPolynomialOutput poly (inactiveCoord i) (∏ l, p l ^ e l))
        (∏ l, p l ^ e l) gridVolume z b / gridVolume : ℝ) : ℂ) *
          test z (fun j => ZMod.castHom hdiv (ZMod q) (b j))) =
      inactive.complexMean (fun i =>
        (FiniteProbabilityWeights.uniform (V → ZMod q)).complexMean (fun r =>
          test (gridPoint i) (fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
            (Sum.elim (fun v => (cLong v : ZMod q) + (step : ZMod q) * r v)
              (fun a => (inactiveCoord i a : ZMod q))) (poly j)))) := by
  rw [rationalInactiveForecast_divisor_tsum_test _ _ _ _ hdiv hV]
  apply congrArg inactive.complexMean
  funext i
  simp_rw [integerLongPolynomialOutput_reduce poly (inactiveCoord i) hdiv]
  exact crtPolynomialInputLaw_arbitrary_step_divisor_complexMean p e step hp hstep
    hcoprime cLong hdiv
    (fun r => test (gridPoint i) (fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
      (Sum.elim r (fun a => (inactiveCoord i a : ZMod q))) (poly j)))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "AI" => PrincipalTupleIndex (fun a : Active => B (Subtype.val a))
  (fun a : Active => degree (Subtype.val a))
local notation "sides" => allocatedPrincipalSides B U basis S

variable (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (deck : ∀ j : Fin m,
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis short j →
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)

theorem allocatedJointResidueOutput_join
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (q : ℕ) (rG : G → ZMod q)
    (u : PrincipalAxisTuples (α := Empty) short sides) (ar : AI → ZMod q) :
    allocatedJointResidueOutput B U basis S base noise deck projection q rG
        (allocatedPrincipalResidueJoin B U basis S q u ar) =
      fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (Sum.elim (Sum.elim rG ar)
          (fun k => (allocatedShortPrincipalRaw B U basis S u k : ZMod q)))
        (allocatedForecastPolynomial short base noise deck projection o) := by
  funext o
  have hlong : (fun j : AI => allocatedPrincipalResidueJoin B U basis S q u ar
      ⟨j.1.val, j.2⟩ none) = ar := by
    funext j
    simp only [allocatedPrincipalResidueJoin, principalAxisResidueJoin, j.1.property, dite_false]
  unfold allocatedJointResidueOutput
  rw [hlong]
  apply allocatedForecastPolynomial_eval₂_raw_congr
  intro j hj
  simp only [allocatedPrincipalResidueJoin, principalAxisResidueJoin,
    allocatedShortPrincipalRaw, hj, dite_true]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

private theorem affineReference_uniform_sum_flip
    {G A R : Type*} [Fintype G] [Fintype A] [Fintype R] [Nonempty R]
    [DecidableEq G] [DecidableEq A] [DecidableEq (G ⊕ A)]
    (f : (G ⊕ A → R) → ℂ) :
    (FiniteProbabilityWeights.uniform (A → R)).complexMean (fun a =>
      (FiniteProbabilityWeights.uniform (G → R)).complexMean (fun g => f (Sum.elim g a))) =
        (FiniteProbabilityWeights.uniform (G ⊕ A → R)).complexMean f := by
  simp only [FiniteProbabilityWeights.uniform_complexMean]
  calc
    _ = 𝔼 ga : (G → R) × (A → R), f (Sum.elim ga.1 ga.2) := by
      rw [Finset.expect_comm]
      simpa only [Finset.univ_product_univ] using
        (Finset.expect_product' (Finset.univ : Finset (G → R))
          (Finset.univ : Finset (A → R)) (fun g a => f (Sum.elim g a))).symm
    _ = _ := by
      apply Fintype.expect_equiv (Equiv.sumPiEquivProdPi (fun _ : G ⊕ A => R)).symm
      intro ga
      rfl

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Long" => LayerSamplerLongVariables short G B
local notation "Active" => PrincipalTupleIndex
  (fun a : {a // ¬short a} => B (Subtype.val a))
  (fun a : {a // ¬short a} => degree (Subtype.val a))
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)

variable (H parameterStep : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (start : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (parameterStep j : ℤ) * t.val ∧
    start j + (parameterStep j : ℤ) * t.val < allocatedPrincipalSides B U basis S j)
variable (hH : ∀ j, 0 < H j)

variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "N" => (∏ l, primes l ^ exponent l)

attribute [local instance] OAI.Erdos3.VectorPolynomial.affineFixedPathCRTModulusNeZero
theorem allocatedAffineFixedPath_crtRationalForecast_reference
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (xref : G → IntegerScalarCubeBox Empty S.value)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (commonStep : ℕ) (hstep : commonStep ≠ 0) (cLong : Long → ℤ)
    (hp : ∀ l, (primes l).Prime)
    (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
    {q : ℕ} [NeZero q] (hq : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (test : (A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      (Out → ZMod q) → ℂ) :
    let poly := allocatedForecastPolynomial short base noise deck projection
    let c := allocatedOriginalSampleInactiveCoefficients B selected sample
    (allocatedInactiveAffineIntervalLaw B U basis S H parameterStep start hinside hH).complexMean (fun u =>
      (FiniteProbabilityWeights.uniform (Long → ZMod q)).complexMean (fun r =>
        test (forecastInactiveShortGrid B U basis S selected c u)
          (fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
            (Sum.elim (fun v => (cLong v : ZMod q) + (commonStep : ZMod q) * r v)
              (fun k => (allocatedShortPrincipalRaw B U basis S u k : ZMod q))) (poly o)))) =
      ∑' z, 𝔼 b : Out → ZMod N,
        ((rationalInactiveForecast (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S)
      H parameterStep start hinside hH)
          (fun _ => crtPolynomialInputLaw primes exponent
            (fun l => padicValNat (primes l) commonStep) hcoprime
            (fun l v => (cLong v : ZMod (primes l ^ exponent l))))
          (forecastInactiveFixedOutput B U basis S selected c xref)
          (fun v => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N)
          N gridVolume z b / gridVolume : ℝ) : ℂ) *
            test z (fun j => ZMod.castHom hq (ZMod q) (b j)) := by
  intro poly c
  symm
  rw [rationalInactivePolynomialForecast_arbitraryStepCRT_tsum_marginal (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S)
      H parameterStep start hinside hH)
    (forecastInactiveFixedOutput B U basis S selected c xref)
    primes exponent commonStep hp hstep hcoprime cLong poly
    (fun v k => (v k.1 k.2 : ℤ)) hq hV test]
  change _ = ((principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S)
      H parameterStep start hinside hH).finitePushforward (principalAxisRestrict short)).complexMean _
  rw [FiniteProbabilityWeights.complexMean_finitePushforward]
  apply congrArg (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S)
      H parameterStep start hinside hH).complexMean
  funext v
  rw [forecastInactiveFixedOutput_eq_shortGrid B U basis S hR hσ selected hsmall c
    (allocatedOriginalSampleInactiveCoefficients_supported B selected U basis hR hσ S sample hs)
    xref v]
  apply congrArg (FiniteProbabilityWeights.uniform (Long → ZMod q)).complexMean
  funext r
  congr 1
  funext o
  exact allocatedForecastPolynomial_short_raw B U basis S base noise deck projection q
    (fun k => (cLong k : ZMod q) + (commonStep : ZMod q) * r k) v o

theorem allocatedAffineFixedPath_joint_crtRationalForecast_reference
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (xref : G → IntegerScalarCubeBox Empty S.value)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (commonStep : ℕ) (hstep : commonStep ≠ 0) (cLong : Long → ℤ)
    (hp : ∀ l, (primes l).Prime)
    (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
    {q : ℕ} [NeZero q] (hq : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (test : (A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      (Out → ZMod q) → ℂ) :
    let poly := allocatedForecastPolynomial short base noise deck projection
    let c := allocatedOriginalSampleInactiveCoefficients B selected sample
    (allocatedInactiveAffineIntervalLaw B U basis S H parameterStep start hinside hH).complexMean (fun u =>
      (FiniteProbabilityWeights.uniform (Active → ZMod q)).complexMean (fun ar =>
        (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
          test (forecastInactiveShortGrid B U basis S selected c u)
            (allocatedJointResidueOutput B U basis S base noise deck projection q
              (fun g => (cLong (Sum.inl g) : ZMod q) + (commonStep : ZMod q) * rG g)
              (allocatedPrincipalResidueJoin B U basis S q u
                (fun a => (cLong (Sum.inr a) : ZMod q) + (commonStep : ZMod q) * ar a)))))) =
      ∑' z, 𝔼 b : Out → ZMod N,
        ((rationalInactiveForecast (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S)
      H parameterStep start hinside hH)
          (fun _ => crtPolynomialInputLaw primes exponent
            (fun l => padicValNat (primes l) commonStep) hcoprime
            (fun l v => (cLong v : ZMod (primes l ^ exponent l))))
          (forecastInactiveFixedOutput B U basis S selected c xref)
          (fun v => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N)
          N gridVolume z b / gridVolume : ℝ) : ℂ) *
            test z (fun j => ZMod.castHom hq (ZMod q) (b j)) := by
  intro poly c
  rw [← allocatedAffineFixedPath_crtRationalForecast_reference B U basis S H parameterStep
    start hinside hH primes exponent hR hσ selected hsmall sample hs xref
    base noise deck projection commonStep hstep cLong hp hcoprime hq hV test]
  apply congrArg (allocatedInactiveAffineIntervalLaw B U basis S H parameterStep start hinside hH).complexMean
  funext u
  simp_rw [allocatedJointResidueOutput_join]
  have hlong (ar : Active → ZMod q) (rG : G → ZMod q) :
      Sum.elim
        (fun g => (cLong (Sum.inl g) : ZMod q) + (commonStep : ZMod q) * rG g)
        (fun a => (cLong (Sum.inr a) : ZMod q) + (commonStep : ZMod q) * ar a) =
      (fun v => (cLong v : ZMod q) + (commonStep : ZMod q) * Sum.elim rG ar v) := by
    funext v
    cases v <;> rfl
  simp_rw [hlong]
  exact affineReference_uniform_sum_flip
    (fun r : Long → ZMod q =>
      test (forecastInactiveShortGrid B U basis S selected c u)
        (fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
          (Sum.elim (fun v => (cLong v : ZMod q) + (commonStep : ZMod q) * r v)
            (fun k => (allocatedShortPrincipalRaw B U basis S u k : ZMod q))) (poly o)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedNativeAmbientComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
attribute [local instance] OAI.Erdos3.VectorPolynomial.slicedPhysicalDensityCRTNeZero
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ box) 1)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (h0 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
variable {Cidx : Type*}
variable (selected : Cidx → Σ j : Fin m, Fin (n j))
variable (hshort : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U basis S.value) j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ}
variable (hV : gridVolume ≠ 0)
variable (test : (Cidx → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      ((Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) → ZMod q) → (((Σ _ : X, Unit ⊕ Empty) → ℝ) × ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℂ)
variable {Kφ : ℝ≥0}
variable (htest : ∀ grid residue, LipschitzWith Kφ (test grid residue))
variable (hbound : ∀ grid residue y, ‖test grid residue y‖ ≤ 1)

local notation "actualDensity" => allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box
  integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c
local notation "finiteReference" => allocatedSlicedPhysicalResidueMean B U basis S HP stepP cP hinsideP hHP
  integerFrame cG stepG sample c q selected base deck projection test actualDensity
local notation "rationalReference" => allocatedSlicedPhysicalRationalMean B U basis S primes exponent
  HP stepP cP hinsideP hHP integerFrame cG stepG sample c q selected xref base deck projection
  hcoprime hqN (gridVolume := gridVolume) test actualDensity

include hR hσ hs hshort hp hV in
theorem allocatedSlicedPhysicalResidueMean_eq_rationalMean_s2_oai :
    finiteReference = rationalReference := by
  exact allocatedAffineFixedPath_joint_crtRationalForecast_reference
    B U basis S HP stepP cP hinsideP hHP primes exponent hR hσ selected hshort sample hs xref
    base integerFrame deck projection stepG (Nat.ne_of_gt hstepG) (Sum.elim cG c)
    hp hcoprime hqN hV
    (fun grid residue => ∫ y, test grid residue y ∂realDensityMeasure volume actualDensity)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedSlicedPhysicalResidueMean_eq_rationalMean_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9} := @OAI.Erdos3.VectorPolynomial.allocatedSlicedPhysicalResidueMean_eq_rationalMean_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9}
