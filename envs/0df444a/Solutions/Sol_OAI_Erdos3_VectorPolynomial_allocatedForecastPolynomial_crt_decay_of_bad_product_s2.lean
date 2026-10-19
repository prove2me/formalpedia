-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedForecastPolynomial_crt_decay_of_bad_product_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:34:53.127984+00:00
-- url     : https://prove2.me/submissions/394ac046-52e9-43d0-b418-377a35962487

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B246
import Theorems.Thm_OAI_Erdos3_primePower_polynomial_image_characteristic_decay_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ModularDecayBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem modular_prod_rpow {ι : Type*} (S : Finset ι) (v : ι → ℝ)
    (hv : ∀ i ∈ S, 0 ≤ v i) (P : ℝ) :
    (∏ i ∈ S, v i ^ P) = (∏ i ∈ S, v i) ^ P := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Real.mul_rpow
      (hv i (Finset.mem_insert_self _ _))
      (Finset.prod_nonneg (fun j hj => hv j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hv j (Finset.mem_insert_of_mem hj))]

theorem modular_product_decay_budget {ι : Type*} (S : Finset ι)
    (c q : ι → ℝ) (z : ι → ℂ) (P₁ P : ℝ)
    (hc : ∀ i ∈ S, 0 ≤ c i) (hq : ∀ i ∈ S, 0 ≤ q i)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ c i ^ P₁ * q i ^ (-P)) :
    ‖∏ i ∈ S, z i‖ ≤ (∏ i ∈ S, c i) ^ P₁ * (∏ i ∈ S, q i) ^ (-P) := by
  rw [norm_prod]
  calc
    _ ≤ ∏ i ∈ S, (c i ^ P₁ * q i ^ (-P)) :=
      Finset.prod_le_prod (fun i _ => norm_nonneg _) hz
    _ = _ := by
      rw [Finset.prod_mul_distrib, modular_prod_rpow S c hc, modular_prod_rpow S q hq]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] {Ω : J → Type*} [∀ j, Fintype (Ω j)]

theorem complexMean_pi_product (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (v : ∀ j, Ω j → ℂ) :
    (pi p).complexMean (fun x => ∏ j, v j (x j)) = ∏ j, (p j).complexMean (v j) := by
  classical
  change (∑ x : ∀ j, Ω j, ((∏ j, (p j).weight (x j) : ℝ) : ℂ) * (∏ j, v j (x j))) =
    ∏ j, ∑ x, ((p j).weight x : ℂ) * v j x
  simp_rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j (x : Ω j) => ((p j).weight x : ℂ) * v j x)).symm

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductImageDecay
namespace OAI

section

namespace Erdos3
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {H : J → Type*} [∀ j, AddCommGroup (H j)]

theorem finiteProductCharacter_single (χ : ∀ j, AddChar (H j) ℂ) (j : J) (x : H j) :
    finiteProductCharacter χ (Pi.single j x) = χ j x := by
  change (∏ i, χ i (Pi.single j x i)) = _
  rw [Finset.prod_eq_single j]
  · rw [Pi.single_eq_same]
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij, AddChar.map_zero_eq_one]
  · simp

theorem finiteProductCharacter_injective : Function.Injective
    (finiteProductCharacter (H := H)) := by
  intro χ ψ h
  funext j
  apply AddChar.ext
  intro x
  have := congrArg (fun θ : AddChar (∀ j, H j) ℂ => θ (Pi.single j x)) h
  simpa only [finiteProductCharacter_single] using this

theorem finiteProductCharacter_decomposition (χ : AddChar (∀ j, H j) ℂ) :
    finiteProductCharacter (finiteProductCharacterCoordinate χ) = χ := by
  ext x
  change (∏ j, χ (Pi.single j (x j))) = χ x
  have hsum : (∑ j, Pi.single j (x j)) = x := by
    ext i
    simp only [Finset.sum_apply, Finset.sum_pi_single, Finset.mem_univ, ite_true]
  have h := map_sum χ.toAddMonoidHom (fun j => Pi.single j (x j)) Finset.univ
  change χ (∑ j, Pi.single j (x j)) = ∏ j, χ (Pi.single j (x j)) at h
  exact (hsum ▸ h).symm

theorem finiteProductCharacter_order (χ : ∀ j, AddChar (H j) ℂ)
    (hcop : Pairwise (fun i j => Nat.Coprime (orderOf (χ i)) (orderOf (χ j)))) :
    orderOf (finiteProductCharacter χ) = ∏ j, orderOf (χ j) := by
  rw [orderOf_injective finiteProductCharacter finiteProductCharacter_injective χ,
    Pi.orderOf]
  exact Finset.lcm_eq_prod (fun i _ j _ hij => hcop hij)

variable [∀ j, Fintype (H j)] {X : J → Type*} [∀ j, Fintype (X j)]

omit [∀ j, Fintype (H j)] in

theorem finiteImageCharacteristic_product (p : ∀ j, FiniteProbabilityWeights (X j))
    (Y : ∀ j, X j → H j) (χ : ∀ j, AddChar (H j) ℂ) :
    finiteImageCharacteristic (FiniteProbabilityWeights.pi p)
      (fun x j => Y j (x j)) (finiteProductCharacter χ) =
      ∏ j, finiteImageCharacteristic (p j) (Y j) (χ j) :=
  FiniteProbabilityWeights.complexMean_pi_product p (fun j x => χ j (Y j x))

omit [∀ j, Fintype (H j)] in

theorem finiteImageCharacteristic_product_decay
    (p : ∀ j, FiniteProbabilityWeights (X j)) (Y : ∀ j, X j → H j)
    (χ : ∀ j, AddChar (H j) ℂ) (c : J → ℝ) (P₁ P : ℝ)
    (hc : ∀ j, 0 ≤ c j)
    (hcop : Pairwise (fun i j => Nat.Coprime (orderOf (χ i)) (orderOf (χ j))))
    (hdecay : ∀ j, ‖finiteImageCharacteristic (p j) (Y j) (χ j)‖ ≤
      c j ^ P₁ * (orderOf (χ j) : ℝ) ^ (-P)) :
    ‖finiteImageCharacteristic (FiniteProbabilityWeights.pi p)
      (fun x j => Y j (x j)) (finiteProductCharacter χ)‖ ≤
      (∏ j, c j) ^ P₁ * (orderOf (finiteProductCharacter χ) : ℝ) ^ (-P) := by
  rw [finiteImageCharacteristic_product, finiteProductCharacter_order χ hcop,
    Nat.cast_prod]
  exact modular_product_decay_budget Finset.univ c (fun j => orderOf (χ j))
    (fun j => finiteImageCharacteristic (p j) (Y j) (χ j)) P₁ P
    (fun j _ => hc j) (fun j _ => Nat.cast_nonneg _) (fun j _ => hdecay j)

omit [Fintype J] [∀ j, Fintype (H j)] in

theorem finiteProductCharacterCoordinate_order_dvd
    (χ : AddChar (∀ j, H j) ℂ) (q : J → ℕ)
    (hkill : ∀ j (x : H j), q j • x = 0) (j : J) :
    orderOf (finiteProductCharacterCoordinate χ j) ∣ q j := by
  apply orderOf_dvd_of_pow_eq_one
  ext x
  rw [AddChar.pow_apply, ← AddChar.map_nsmul_eq_pow, hkill, AddChar.map_zero_eq_one,
    AddChar.one_apply]

omit [Fintype J] [∀ j, Fintype (H j)] in

theorem finiteProductCharacterCoordinate_coprime
    (χ : AddChar (∀ j, H j) ℂ) (q : J → ℕ)
    (hkill : ∀ j (x : H j), q j • x = 0)
    (hq : Pairwise (fun i j => Nat.Coprime (q i) (q j))) :
    Pairwise (fun i j => Nat.Coprime (orderOf (finiteProductCharacterCoordinate χ i))
      (orderOf (finiteProductCharacterCoordinate χ j))) := by
  intro i j hij
  exact (hq hij).of_dvd (finiteProductCharacterCoordinate_order_dvd χ q hkill i)
    (finiteProductCharacterCoordinate_order_dvd χ q hkill j)

omit [∀ j, Fintype (H j)] in

theorem finiteImageCharacteristic_crt_decay {G : Type*} [AddCommGroup G] [Fintype G]
    (e : G ≃+ (∀ j, H j)) (p : ∀ j, FiniteProbabilityWeights (X j))
    (Y : ∀ j, X j → H j) (q : J → ℕ)
    (hkill : ∀ j (x : H j), q j • x = 0)
    (hq : Pairwise (fun i j => Nat.Coprime (q i) (q j)))
    (c : J → ℝ) (P₁ P : ℝ) (hc : ∀ j, 0 ≤ c j)
    (hdecay : ∀ j (ψ : AddChar (H j) ℂ),
      ‖finiteImageCharacteristic (p j) (Y j) ψ‖ ≤ c j ^ P₁ * (orderOf ψ : ℝ) ^ (-P))
    (χ : AddChar G ℂ) :
    ‖finiteImageCharacteristic (FiniteProbabilityWeights.pi p)
      (fun x => e.symm (fun j => Y j (x j))) χ‖ ≤
      (∏ j, c j) ^ P₁ * (orderOf χ : ℝ) ^ (-P) := by
  let ψ := characterPullback e.symm.toAddMonoidHom χ
  have hord : orderOf ψ = orderOf χ :=
    characterPullback_order e.symm.toAddMonoidHom e.symm.surjective χ
  have h := finiteImageCharacteristic_product_decay p Y
    (finiteProductCharacterCoordinate ψ) c P₁ P hc
    (finiteProductCharacterCoordinate_coprime ψ q hkill hq)
    (fun j => hdecay j _)
  rw [finiteProductCharacter_decomposition, hord] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PolynomialCharacterRowPhase
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I V R S : Type*} [Fintype I] [CommRing R] [CommRing S]

theorem map_homogeneousComponent (φ : R →+* S) (d : ℕ) (P : MvPolynomial V R) :
    map φ (homogeneousComponent d P) = homogeneousComponent d (map φ P) := by
  ext e
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

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

theorem crtInput_integerPolynomial_eval (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (F : MvPolynomial V ℤ) (x : ∀ l : L, V → ZMod (q l)) (l : L) :
    ZMod.prodEquivPi q hq
      (MvPolynomial.eval₂ (Int.castRingHom (ZMod (∏ k, q k))) (crtInput q hq x) F) l =
        MvPolynomial.eval₂ (Int.castRingHom (ZMod (q l))) (x l) F := by
  let e := ZMod.prodEquivPi q hq
  let φ := (Pi.evalRingHom (fun k => ZMod (q k)) l).comp e.toRingHom
  change φ (MvPolynomial.eval₂ _ _ F) = _
  rw [MvPolynomial.hom_eval₂]
  have hc : φ.comp (Int.castRingHom (ZMod (∏ k, q k))) =
      Int.castRingHom (ZMod (q l)) := Subsingleton.elim _ _
  rw [hc]
  congr 1
  funext v
  exact congrFun (e.apply_symm_apply (fun k => x k v)) l

theorem taggedOutputCRTEquiv_integerPolynomial_eval (J : Tag → Type*) (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (F : ∀ h : Tag, J h → MvPolynomial V ℤ) (x : ∀ l : L, V → ZMod (q l)) :
    taggedOutputCRTEquiv J q hq
      (fun h j => MvPolynomial.eval₂ (Int.castRingHom (ZMod (∏ l, q l)))
        (crtInput q hq x) (F h j)) =
      fun l h j => MvPolynomial.eval₂ (Int.castRingHom (ZMod (q l))) (x l) (F h j) := by
  funext l h j
  exact crtInput_integerPolynomial_eval q hq (F h j) x l

theorem taggedOutputCRTEquiv_symm_integerPolynomial_eval (J : Tag → Type*) (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (F : ∀ h : Tag, J h → MvPolynomial V ℤ) (x : ∀ l : L, V → ZMod (q l)) :
    (taggedOutputCRTEquiv J q hq).symm
      (fun l h j => MvPolynomial.eval₂ (Int.castRingHom (ZMod (q l))) (x l) (F h j)) =
      fun h j => MvPolynomial.eval₂ (Int.castRingHom (ZMod (∏ l, q l)))
        (crtInput q hq x) (F h j) := by
  apply (taggedOutputCRTEquiv J q hq).injective
  rw [AddEquiv.apply_symm_apply]
  exact (taggedOutputCRTEquiv_integerPolynomial_eval J q hq F x).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I R S : Type*} [CommRing R] [CommRing S]

theorem polynomialTranslate_map_coefficients (φ : R →+* S) (u : I → R)
    (P : MvPolynomial I R) :
    map φ (polynomialTranslate u P) =
      polynomialTranslate (fun i => φ (u i)) (map φ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, map_X, polynomialTranslate_X, map_add, map_C, hP]

end Erdos3


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem map_integerPolynomial_homogeneousComponent
    {V : Type*} (p A B d : ℕ) [NeZero p] (hBA : B ≤ A)
    (F : MvPolynomial V ℤ) :
    map (ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B)))
      (homogeneousComponent d (map (Int.castRingHom (ZMod (p ^ A))) F)) =
      map (Int.castRingHom (ZMod (p ^ B))) (homogeneousComponent d F) := by
  have hcomp : (ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B))).comp
      (Int.castRingHom (ZMod (p ^ A))) = Int.castRingHom (ZMod (p ^ B)) :=
    RingHom.eq_intCast' _
  rw [← map_homogeneousComponent, MvPolynomial.map_map, hcomp]

theorem primePowerHomogeneousRankProbability_integerPolynomial
    {V J : Type*} [Fintype V] [Fintype J]
    (p A B n : ℕ) [NeZero p] (hBA : B ≤ A)
    (F : J → MvPolynomial V ℤ) (row : J → ZMod (p ^ B)) :
    primePowerHomogeneousRankProbability p A B n hBA
      (fun i => map (Int.castRingHom (ZMod (p ^ A))) (F i)) row =
      integerPolynomialRankProbability p B n F row := by
  unfold primePowerHomogeneousRankProbability integerPolynomialRankProbability
  have hF : (fun i => map (ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B)))
      (homogeneousComponent (n + 1) (map (Int.castRingHom (ZMod (p ^ A))) (F i)))) =
      (fun i => map (Int.castRingHom (ZMod (p ^ B)))
        (homogeneousComponent (n + 1) (F i))) := by
    funext i
    exact map_integerPolynomial_homogeneousComponent p A B (n + 1) hBA (F i)
  rw [hF]

end Erdos3


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem crt_integer_polynomial_characteristic_decay
    {L V : Type*} [Fintype L] [Fintype V] {s : ℕ} (hs : 0 < s)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A b e : L → ℕ) [∀ l, NeZero (p l)]
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (C : ℝ) (hC : 0 ≤ C)
    (F : ∀ j, J j → MvPolynomial V ℤ)
    (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
    (hrank : ∀ (l : L) (B : ℕ) (_ : b l < B) (_hBA : B ≤ A l) (j : Fin s)
      (row : J j → ZMod (p l ^ B)), (∃ i, IsUnit (row i)) →
      integerPolynomialRankProbability (p l) B j.val (F j) row ≤
        (p l : ℝ) ^ (-C * B))
    (r : ∀ l, V → ZMod (p l ^ A l))
    (χ : AddChar (∀ j, J j → ZMod (∏ l, p l ^ A l)) ℂ) :
    ‖finiteImageCharacteristic
      (FiniteProbabilityWeights.pi (fun l => FiniteProbabilityWeights.uniform (V → ZMod (p l ^ A l))))
      (fun x j i => eval₂ (Int.castRingHom (ZMod (∏ l, p l ^ A l)))
        (crtInput (fun l => p l ^ A l) (primePower_crt_coprime p A hp hinj)
          (fun l v => r l v + (p l : ZMod (p l ^ A l)) ^ e l * x l v)) (F j i)) χ‖ ≤
      (∏ l, ((p l ^ (b l + e l) : ℕ) : ℝ)) ^
        (modularRankDecayExponent s C * modularRankChargeFactor s) *
          (orderOf χ : ℝ) ^ (-modularRankDecayExponent s C) := by
  let q : L → ℕ := fun l => p l ^ A l
  let : ∀ l, NeZero (q l) := fun l => inferInstanceAs (NeZero (p l ^ A l))
  let : NeZero (∏ l, q l) := ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => NeZero.ne (q l))⟩
  let hq := primePower_crt_coprime p A hp hinj
  let E := taggedOutputCRTEquiv J q hq
  let law := fun l => FiniteProbabilityWeights.uniform (V → ZMod (q l))
  let Y : ∀ l, (V → ZMod (q l)) → (∀ j, J j → ZMod (q l)) :=
    fun l x j i => eval₂ (Int.castRingHom (ZMod (q l)))
      (fun v => r l v + (p l : ZMod (q l)) ^ e l * x v) (F j i)
  let cap : L → ℝ := fun l => ((p l ^ (b l + e l) : ℕ) : ℝ)
  have hkill : ∀ l (z : ∀ j, J j → ZMod (q l)), q l • z = 0 := by
    intro l z
    ext j i
    simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  have hlocal (l : L) (ψ : AddChar (∀ j, J j → ZMod (q l)) ℂ) :
      ‖finiteImageCharacteristic (law l) (Y l) ψ‖ ≤
        cap l ^ (modularRankDecayExponent s C * modularRankChargeFactor s) *
          (orderOf ψ : ℝ) ^ (-modularRankDecayExponent s C) := by
    have hFl : ∀ j i, (map (Int.castRingHom (ZMod (p l ^ A l))) (F j i)).totalDegree ≤
        j.val + 1 := by
      intro j i
      apply le_trans _ (hF j i)
      exact Finset.sup_mono (support_map_subset _ _)
    have h := primePower_polynomial_image_characteristic_decay_s2 hs (p l) (A l) (b l) (e l)
      (hp l) C hC (fun j i => map (Int.castRingHom (ZMod (p l ^ A l))) (F j i))
      hFl (by
        intro B hbB hBA j row hunit
        rw [primePowerHomogeneousRankProbability_integerPolynomial]
        exact hrank l B hbB hBA j row hunit) (r l) ψ
    simpa only [eval_map, law, Y, cap, q] using h
  have hglobal := finiteImageCharacteristic_crt_decay E law Y q hkill hq cap
    (modularRankDecayExponent s C * modularRankChargeFactor s)
    (modularRankDecayExponent s C) (fun l => Nat.cast_nonneg _) hlocal χ
  have houtput : (fun x : ∀ l, V → ZMod (q l) => E.symm (fun l => Y l (x l))) =
      (fun x j i => eval₂ (Int.castRingHom (ZMod (∏ l, p l ^ A l)))
        (crtInput (fun l => p l ^ A l) hq
          (fun l v => r l v + (p l : ZMod (p l ^ A l)) ^ e l * x l v)) (F j i)) := by
    funext x
    exact taggedOutputCRTEquiv_symm_integerPolynomial_eval J q hq F
      (fun l v => r l v + (p l : ZMod (p l ^ A l)) ^ e l * x l v)
  rw [houtput] at hglobal
  exact hglobal

end Erdos3


namespace Erdos3
open scoped BigOperators Classical

theorem largestTestedBadDepth_not_bad {Ω : Type*} (A : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (p : ℕ) (x : Ω) {a : ℕ}
    (ha : largestTestedBadDepth A bad p x < a) (hA : a ≤ A p) : ¬ bad p a x := by
  intro hbad
  have hmem : a ∈ (Finset.Icc 1 (A p)).filter (fun a => bad p a x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hA⟩, hbad⟩
  exact (not_le_of_gt ha) (Finset.le_sup (f := id) hmem)

theorem crtPolynomialCharge_le_of_bad_product {L : Type*} [Fintype L]
    (p b e : L → ℕ) (s : ℕ) {C : ℝ} (hC : 0 ≤ C) {R : ℕ}
    (hbad : (∏ l, p l ^ b l) ≤ R) :
    crtPolynomialCharge p b e s C ≤
      ((R * ∏ l, p l ^ e l : ℕ) : ℝ) ^
        (modularRankDecayExponent s C * modularRankChargeFactor s) := by
  have hP : 0 ≤ modularRankDecayExponent s C := by
    unfold modularRankDecayExponent
    positivity
  unfold crtPolynomialCharge
  apply Real.rpow_le_rpow (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) ?_
    (mul_nonneg hP (Nat.cast_nonneg _))
  rw [← Nat.cast_prod]
  exact_mod_cast (show (∏ l, p l ^ (b l + e l)) ≤ R * ∏ l, p l ^ e l from by
    simp_rw [pow_add]
    rw [Finset.prod_mul_distrib]
    exact Nat.mul_le_mul_right _ hbad)

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularMultilinearAmbientSublevel
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Classical BigOperators

variable {I J R : Type*} [CommRing R]

theorem eval_conditionPolynomial (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) (y : J → R) :
    eval y (conditionPolynomial f hf v P) = eval (Function.extend f y v) P := by
  unfold conditionPolynomial
  induction P using MvPolynomial.induction_on with
  | C c => simp only [polynomialTranslate_C, killCompl_C, eval_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP, polynomialTranslate_X, map_add, killCompl_C, eval_C, eval_X]
    congr 1
    by_cases hi : i ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hi
      simp only [show f j ∈ Set.range f from ⟨j, rfl⟩, ite_true, add_zero,
        hf.extend_apply]
      rw [← rename_X f j, killCompl_rename_app, eval_X]
    · simp only [hi, ite_false, Function.extend_apply' y v i hi]
      have hz : killCompl hf (X i : MvPolynomial I R) = 0 := by
        simp only [killCompl, aeval_X, hi, dite_false]
      rw [hz, map_zero, zero_add]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

theorem modularBoundedCoefficientPolynomial_degree {K R : Type*}
    [Fintype K] [CommRing R] (h : ℕ)
    (c : BoundedCoefficientExponent K h → R) :
    (modularBoundedCoefficientPolynomial h c).totalDegree ≤ h := by
  unfold modularBoundedCoefficientPolynomial
  apply totalDegree_finsetSum_le
  intro e _
  exact (totalDegree_monomial_le e.val (c e)).trans e.property

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialInputAffineLaw
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

omit [Fintype V] in

theorem crtPrimePowerIntegerPolynomialOutput_reduce {s : ℕ} {J : Fin s → Type*}
    (p A e : L → ℕ) [NeZero (∏ l, p l ^ A l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (F : ∀ j, J j → MvPolynomial V ℤ) (r : ∀ l, V → ZMod (p l ^ A l))
    (x : ∀ l, V → ZMod (p l ^ A l)) (j : Sigma J) :
    (crtPrimePowerIntegerPolynomialOutput p A e hq F r x j : ZMod (∏ l, p l ^ A l)) =
      crtPrimePowerPolynomialMap p A e hq F r x j.1 j.2 := by
  unfold crtPrimePowerIntegerPolynomialOutput crtPrimePowerPolynomialMap
  change (Int.castRingHom (ZMod (∏ l, p l ^ A l))) (eval₂ (RingHom.id ℤ) _ _) = _
  rw [MvPolynomial.hom_eval₂, RingHom.comp_id]
  congr 1
  funext v
  simp only [Int.coe_castRingHom, Int.cast_natCast, ZMod.natCast_zmod_val]

section RankBounds

variable {s : ℕ} (hs : 0 < s) {J : Fin s → Type*} [∀ j, Fintype (J j)]
  (p A b e : L → ℕ) [∀ l, NeZero (p l)]
  (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
  (C : ℝ) (hC : 0 ≤ C)
  (F : ∀ j, J j → MvPolynomial V ℤ)
  (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
  (hrank : ∀ (l : L) (B : ℕ), b l < B → B ≤ A l → ∀ (j : Fin s)
    (row : J j → ZMod (p l ^ B)), (∃ i, IsUnit (row i)) →
    integerPolynomialRankProbability (p l) B j.val (F j) row ≤ (p l : ℝ) ^ (-C * B))
  (r : ∀ l, V → ZMod (p l ^ A l))

include hs hp hinj hC hF hrank

theorem crt_integer_polynomial_rational_characteristic_decay
    (χ : AddChar (Sigma J → ZMod (∏ l, p l ^ A l)) ℂ) :
    ‖finiteImageCharacteristic (crtPrimePowerPolynomialLaw (V := V) p A)
      (fun x j => (crtPrimePowerIntegerPolynomialOutput p A e
        (primePower_crt_coprime p A hp hinj) F r x j : ZMod (∏ l, p l ^ A l))) χ‖ ≤
      crtPolynomialCharge p b e s C * (orderOf χ : ℝ) ^ (-modularRankDecayExponent s C) := by
  let : NeZero (∏ l, p l ^ A l) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
  let E := taggedPolynomialOutputCurry J (∏ l, p l ^ A l)
  let ψ := characterPullback E.symm.toAddMonoidHom χ
  have ho : orderOf ψ = orderOf χ :=
    characterPullback_order E.symm.toAddMonoidHom E.symm.surjective χ
  have h := crt_integer_polynomial_characteristic_decay hs p A b e hp hinj C hC F hF hrank r ψ
  rw [ho] at h
  simp_rw [crtPrimePowerIntegerPolynomialOutput_reduce]
  exact h

end RankBounds

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

attribute [local instance] OAI.Erdos3.crtInputModulusNeZero
theorem crtPolynomialInputLaw_complexMean
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    (f : (V → ZMod (∏ l, p l ^ A l)) → ℂ) :
    (crtPolynomialInputLaw p A e hq origin).complexMean f =
      (crtPrimePowerPolynomialLaw (V := V) p A).complexMean
        (fun x => f (prescribedCRTPolynomialInput p A e hq origin x)) :=
  FiniteProbabilityWeights.fiberLaw_complexMean _ _ _

theorem crtPolynomialInputLaw_integerLong_characteristic
    {Inactive Out : Type*}
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    (poly : Out → MvPolynomial (V ⊕ Inactive) ℤ) (inactive : Inactive → ℤ)
    (χ : AddChar (Out → ZMod (∏ l, p l ^ A l)) ℂ) :
    finiteImageCharacteristic (crtPolynomialInputLaw p A e hq origin)
      (fun t j => (integerLongPolynomialOutput poly inactive (∏ l, p l ^ A l) t j :
        ZMod (∏ l, p l ^ A l))) χ =
    finiteImageCharacteristic (crtPrimePowerPolynomialLaw (V := V) p A)
      (fun x j => (MvPolynomial.eval
        (Sum.elim (fun v => ((prescribedCRTPolynomialInput p A e hq origin x v).val : ℤ))
          inactive) (poly j) : ZMod (∏ l, p l ^ A l))) χ :=
  crtPolynomialInputLaw_complexMean p A e hq origin _

theorem crtPolynomialInputLaw_integerLong_characteristic_of_output
    {Inactive Out : Type*}
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    (poly : Out → MvPolynomial (V ⊕ Inactive) ℤ) (inactive : Inactive → ℤ)
    (Y : (∀ l, V → ZMod (p l ^ A l)) → Out → ℤ)
    (hY : ∀ x j, Y x j = MvPolynomial.eval
      (Sum.elim (fun v => ((prescribedCRTPolynomialInput p A e hq origin x v).val : ℤ))
        inactive) (poly j))
    (χ : AddChar (Out → ZMod (∏ l, p l ^ A l)) ℂ) :
    finiteImageCharacteristic (crtPolynomialInputLaw p A e hq origin)
      (fun t j => (integerLongPolynomialOutput poly inactive (∏ l, p l ^ A l) t j :
        ZMod (∏ l, p l ^ A l))) χ =
    finiteImageCharacteristic (crtPrimePowerPolynomialLaw (V := V) p A)
      (fun x j => (Y x j : ZMod (∏ l, p l ^ A l))) χ := by
  rw [crtPolynomialInputLaw_integerLong_characteristic]
  apply congrArg (fun F => finiteImageCharacteristic (crtPrimePowerPolynomialLaw (V := V) p A) F χ)
  funext x j
  rw [hY]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

theorem samplerLongEmbedding_dedicated_mem_range (inactive : D → Prop) (h : D → ℕ)
    (d : D) (b : B d) (v : Fin (h d)) :
    (Sum.inr ⟨d, b, v⟩ : SamplerTupleIndex G B h) ∈
      Set.range (samplerLongEmbedding inactive h) ↔ ¬ inactive d := by
  constructor
  · rintro ⟨k, hk⟩
    rcases k with g | ⟨a, c, w⟩
    · simp only [samplerLongEmbedding_common, Sum.inl_ne_inr] at hk
    · have he : a.val = d := congrArg Sigma.fst (Sum.inr.inj hk)
      exact he ▸ a.property
  · intro hd
    exact ⟨.inr ⟨⟨d, hd⟩, b, v⟩, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankBadProduct
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

section RingMap

variable {K L A R S : Type*} [CommRing R] [CommRing S]

theorem homogeneousComponent_map_ringHom (f : R →+* S) (h : ℕ) (P : MvPolynomial K R) :
    homogeneousComponent h (P.map f) = (homogeneousComponent h P).map f := by
  ext a
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp only [map_zero]

theorem modularBoundedCoefficientPolynomial_map [Fintype K]
    (f : R →+* S) (h : ℕ) (c : BoundedCoefficientExponent K h → R) :
    modularBoundedCoefficientPolynomial h (fun e => f (c e)) =
      (modularBoundedCoefficientPolynomial h c).map f := by
  simp only [modularBoundedCoefficientPolynomial, map_sum, MvPolynomial.map_monomial]

end RingMap

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

theorem allocatedCongruenceModulusBad_good (C : ℝ) (N : ℕ) [NeZero N]
    (x : AllocatedCongruenceScalarIndex X E inactive L → ZMod N)
    (hgood : ¬ allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C N x)
    (v : LayerSamplerVariables G I n B → ZMod N) (j : Fin m)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod N) (hw : ∃ o, IsUnit (w o)) :
    allocatedCongruenceRankFailureProbability inactive j (fun q => (noise q : ZMod N))
      (fun j q i => (r j q i : ZMod N)) (fun b q => (projection j b q : ZMod N))
      spatial (kernel j) (block j) (fun o l => x ⟨j,(o,l)⟩) v w ≤ (N : ℝ) ^ (-C) :=
  le_of_not_gt (fun hbad => hgood ⟨v, j, w, hw, hbad⟩)

theorem allocatedCongruenceRankBad_good
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ)
    (p : P) (a : ℕ) (x : AllocatedCongruenceScalarIndex X E inactive L → ℤ)
    (hgood : ¬ allocatedCongruenceRankBad inactive noise r projection spatial kernel block
      P C p.val a x)
    (v : LayerSamplerVariables G I n B → ZMod (p.val ^ a)) (j : Fin m)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod (p.val ^ a))
    (hw : ∃ o, IsUnit (w o)) :
    allocatedCongruenceRankFailureProbability inactive j (fun q => (noise q : ZMod (p.val ^ a)))
      (fun j q i => (r j q i : ZMod (p.val ^ a)))
      (fun b q => (projection j b q : ZMod (p.val ^ a)))
      spatial (kernel j) (block j) (fun o l => (x ⟨j,(o,l)⟩ : ZMod (p.val ^ a))) v w ≤
        ((p.val ^ a : ℕ) : ℝ) ^ (-C) := by
  have hmod : ¬ allocatedCongruenceModulusBad inactive noise r projection spatial kernel block
      C (p.val ^ a) (fun i => (x i : ZMod (p.val ^ a))) :=
    fun hbad => hgood ⟨p.property, hbad⟩
  exact allocatedCongruenceModulusBad_good inactive noise r projection spatial kernel block C
    (p.val ^ a) (fun i => (x i : ZMod (p.val ^ a))) hmod v j w hw

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ConditionPolynomialMapDegree
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Classical BigOperators

variable {I J R S : Type*} [CommRing R] [CommRing S]

theorem conditionPolynomial_totalDegree_le (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) :
    (conditionPolynomial f hf v P).totalDegree ≤ P.totalDegree := by
  let u : I → R := fun i => if i ∈ Set.range f then 0 else v i
  have ht : polynomialTranslate u P ∈ weightedSupportLE (1 : I → ℕ) P.totalDegree := by
    apply weightedSupportLE_aeval (1 : I → ℕ) (1 : I → ℕ)
      (fun i => X i + C (u i))
    · intro i
      exact (weightedSupportLE (1 : I → ℕ) 1).add_mem
        (weightedSupportLE_X _ i) (weightedSupportLE_C _ _ _)
    · exact (mem_weightedSupportLE_one_iff P _).mpr le_rfl
  apply (mem_weightedSupportLE_one_iff _ _).mp
  intro a ha
  change a ∈ (conditionPolynomial f hf v P).support at ha
  have hmem : a.mapDomain f ∈ (polynomialTranslate u P).support := by
    simpa only [conditionPolynomial, u, mem_support_iff, coeff_killCompl] using ha
  have h : Finsupp.weight (fun _ : I => 1) (a.mapDomain f) ≤ P.totalDegree := ht hmem
  change Finsupp.weight (fun _ : J => 1) a ≤ P.totalDegree
  simpa only [← Finsupp.degree_eq_weight_one, Finsupp.degree_mapDomain] using h

theorem conditionPolynomial_map (φ : R →+* S) (f : J → I)
    (hf : Function.Injective f) (v : I → R) (P : MvPolynomial I R) :
    map φ (conditionPolynomial f hf v P) =
      conditionPolynomial f hf (fun i => φ (v i)) (map φ P) := by
  unfold conditionPolynomial
  rw [← killCompl_map, polynomialTranslate_map_coefficients]
  apply congrArg (fun u : I → S => killCompl hf (polynomialTranslate u (map φ P)))
  funext i
  split_ifs <;> simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankIntegerDecay
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

theorem allocatedCongruenceIntegerPolynomial_degree
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (v : LayerSamplerVariables G I n B → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    (allocatedCongruenceIntegerPolynomial inactive j base noise r projection v o).totalDegree ≤
      j.val + 1 := by
  rcases o with x | i | a
  · apply (conditionPolynomial_totalDegree_le _ _ _ _).trans
    apply (totalDegree_add _ _).trans
    apply max_le
    · rw [totalDegree_C]
      exact Nat.zero_le _
    · exact (spatialRankPolynomial_degree _).trans (by omega)
  · exact (conditionPolynomial_totalDegree_le _ _ _ _).trans
      (modularBoundedCoefficientPolynomial_degree _ _)
  · exact (conditionPolynomial_totalDegree_le _ _ _ _).trans
      (modularBoundedCoefficientPolynomial_degree _ _)

theorem allocatedCongruenceIntegerPolynomial_top_reduce
    (N : ℕ) (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (v : LayerSamplerVariables G I n B → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    (homogeneousComponent (j.val + 1)
      (allocatedCongruenceIntegerPolynomial inactive j base noise r projection v o)).map
        (Int.castRingHom (ZMod N)) =
      allocatedOriginalTaggedTop inactive j (fun q => (noise q : ZMod N))
        (fun j q i => (r j q i : ZMod N)) (fun a q => (projection a q : ZMod N))
        (fun k => (v k : ZMod N)) (allocatedCongruenceOutputEmbedding inactive j o) := by
  rw [← homogeneousComponent_map_ringHom]
  rcases o with x | i | a
  · have hx : j.val + 1 = 1 := by simp only [x.property, zero_add]
    simp only [allocatedCongruenceIntegerPolynomial, conditionPolynomial_map,
      allocatedCongruenceOutputEmbedding_spatial, allocatedOriginalTaggedTop, hx,
      map_add, map_C, Int.coe_castRingHom]
    have hs : (spatialRankPolynomial (fun d => noise (d, x.val))).map
        (Int.castRingHom (ZMod N)) =
        spatialRankPolynomial (fun d => (noise (d, x.val) : ZMod N)) := by
      simp only [spatialRankPolynomial, map_sum, MvPolynomial.map_monomial,
        Int.coe_castRingHom]
    rw [hs]
    simp only [conditionPolynomial, map_add, polynomialTranslate_C, killCompl_C]
    have hc : homogeneousComponent 1 (C (base x.val : ZMod N) :
        MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)) = 0 :=
      homogeneousComponent_eq_zero _ _ (by rw [totalDegree_C]; exact zero_lt_one)
    rw [hc, zero_add]
  · simp only [allocatedCongruenceIntegerPolynomial, conditionPolynomial_map,
      allocatedCongruenceOutputEmbedding_deck, allocatedOriginalTaggedTop,
      modularDeckPolynomial, ← modularBoundedCoefficientPolynomial_map,
      Int.coe_castRingHom]
  · simp only [allocatedCongruenceIntegerPolynomial, conditionPolynomial_map,
      allocatedCongruenceOutputEmbedding_integer, allocatedOriginalTaggedTop,
      ← modularBoundedCoefficientPolynomial_map, Int.coe_castRingHom,
      allocatedCongruenceIntegerEmbedding]
    rfl

theorem allocatedCongruenceIntegerPolynomial_top_eq_actual_rank
    (N : ℕ) (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (v : LayerSamplerVariables G I n B → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    (homogeneousComponent (j.val + 1)
      (allocatedCongruenceIntegerPolynomial inactive j base noise r projection v o)).map
        (Int.castRingHom (ZMod N)) =
      allocatedCongruenceRankPolynomial inactive j (fun q => (noise q : ZMod N))
        (fun j q i => (r j q i : ZMod N)) (fun a q => (projection a q : ZMod N))
        spatial kernel block
        (fun z => allocatedSelectedRankCoefficients inactive j (fun q => (noise q : ZMod N))
          (fun j q i => (r j q i : ZMod N)) (fun a q => (projection a q : ZMod N))
          spatial kernel block (allocatedCongruenceOutputEmbedding inactive j z))
        (fun k => (v k : ZMod N)) o := by
  rw [allocatedCongruenceRankPolynomial_original]
  exact allocatedCongruenceIntegerPolynomial_top_reduce N inactive j base noise r projection v o

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

local notation "selected" => allocatedCongruenceIntegerSelectedCoefficients
  inactive noise r projection spatial kernel block

theorem allocatedCongruenceIntegerPolynomial_rank_probability
    (p a : ℕ) [NeZero p] (base : X → ℤ)
    (v : LayerSamplerVariables G I n B → ℤ) (j : Fin m)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod (p ^ a)) :
    integerPolynomialRankProbability p a j.val
      (allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j) v) w =
    allocatedCongruenceRankFailureProbability inactive j (fun q => (noise q : ZMod (p ^ a)))
      (fun j q i => (r j q i : ZMod (p ^ a)))
      (fun b q => (projection j b q : ZMod (p ^ a))) spatial (kernel j) (block j)
      (fun o l => (selected ⟨j,(o,l)⟩ : ZMod (p ^ a))) (fun k => (v k : ZMod (p ^ a))) w := by
  unfold integerPolynomialRankProbability allocatedCongruenceRankFailureProbability
  simp only [allocatedCongruenceIntegerSelectedCoefficients_reduce,
    allocatedCongruenceIntegerPolynomial_top_eq_actual_rank
      (p ^ a) inactive j base noise r (projection j) spatial (kernel j) (block j)]
  simp only [polynomialCharacterRow, smul_eq_C_mul]

theorem allocatedCongruenceIntegerPolynomial_rank_of_good
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ) (p : P) (a : ℕ)
    (hgood : ¬ allocatedCongruenceRankBad inactive noise r projection spatial kernel block
      P C p.val a selected)
    (base : X → ℤ) (v : LayerSamplerVariables G I n B → ℤ) (j : Fin m)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod (p.val ^ a))
    (hw : ∃ o, IsUnit (w o)) :
    integerPolynomialRankProbability p.val a j.val
      (allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j) v) w ≤
      (p.val : ℝ) ^ (-C * a) := by
  rw [allocatedCongruenceIntegerPolynomial_rank_probability inactive noise r projection spatial kernel block]
  have h := allocatedCongruenceRankBad_good inactive noise r projection spatial kernel block
    P C p a selected hgood (fun k => (v k : ZMod (p.val ^ a))) j w hw
  calc
    _ ≤ ((p.val ^ a : ℕ) : ℝ) ^ (-C) := h
    _ = (p.val : ℝ) ^ (-C * a) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p.val)]
      congr 1
      ring

theorem allocatedCongruence_largest_bad_depth_good
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (C : ℝ)
    (p : P) (a : ℕ)
    (ha : largestTestedBadDepth A
      (allocatedCongruenceRankBad inactive noise r projection spatial kernel block P C)
      p.val selected < a) (hA : a ≤ A p.val) :
    ¬ allocatedCongruenceRankBad inactive noise r projection spatial kernel block
      P C p.val a selected :=
  largestTestedBadDepth_not_bad A _ p.val selected ha hA

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankRationalDecay
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

theorem allocatedCongruence_crt_rational_decay_of_bad_product
    (hm : 0 < m) (P : Finset ℕ) [∀ p : P, NeZero p.val]
    (A e : ℕ → ℕ) (hp : ∀ p ∈ P, p.Prime) (C : ℝ) (hC : 0 ≤ C) (R : ℕ)
    (hbad : (∏ p : P, p.val ^ allocatedCongruenceBadDepth
      inactive noise r projection spatial kernel block P A C p.val) ≤ R)
    (base : X → ℤ) (v : LayerSamplerVariables G I n B → ℤ)
    (origin : ∀ p : P, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val))
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X E inactive) →
      ZMod (∏ p : P, p.val ^ A p.val)) ℂ) :
    letI : DecidableEq P := Classical.decEq _
    ‖finiteImageCharacteristic (crtPrimePowerPolynomialLaw (V := LayerSamplerLongVariables inactive G B)
        (fun p : P => p.val) (fun p : P => A p.val))
      (fun x j => (crtPrimePowerIntegerPolynomialOutput (fun p : P => p.val) (fun p : P => A p.val)
        (fun p : P => e p.val)
        (primePower_crt_coprime (fun p : P => p.val) (fun p : P => A p.val)
          (fun p => hp p.val p.property) Subtype.val_injective)
        (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j) v)
        origin x j : ZMod (∏ p : P, p.val ^ A p.val))) χ‖ ≤
      ((R * ∏ p : P, p.val ^ e p.val : ℕ) : ℝ) ^
        (modularRankDecayExponent m C * modularRankChargeFactor m) *
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent m C) := by
  let : DecidableEq P := Classical.decEq _
  let b := allocatedCongruenceBadDepth inactive noise r projection spatial kernel block P A C
  have h := crt_integer_polynomial_rational_characteristic_decay hm
    (fun p : P => p.val) (fun p : P => A p.val) (fun p : P => b p.val) (fun p : P => e p.val)
    (fun p => hp p.val p.property) Subtype.val_injective C hC
    (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j) v)
    (fun j o => allocatedCongruenceIntegerPolynomial_degree inactive j base noise r (projection j) v o)
    (fun p a ha hA j w hw =>
      allocatedCongruenceIntegerPolynomial_rank_of_good inactive noise r projection spatial kernel block
        P C p a (allocatedCongruence_largest_bad_depth_good inactive noise r projection spatial kernel block
          P A C p a ha hA) base v j w hw) origin χ
  exact h.trans (mul_le_mul_of_nonneg_right
    (crtPolynomialCharge_le_of_bad_product (fun p : P => p.val) (fun p : P => b p.val)
      (fun p : P => e p.val) m hC hbad) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SamplerSeparatedVariables
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {D G : Type*} {B : D → Type*}

theorem samplerSeparatedValues_eq_extend {R : Type*} [Zero R]
    (inactive : D → Prop) (h : D → ℕ)
    (long : SamplerLongVariables inactive G B h → R)
    (raw : PrincipalTupleIndex B h × Option Empty → R) :
    Sum.elim long raw ∘ samplerSeparatedVariable inactive h =
      Function.extend (samplerLongEmbedding inactive h) long (samplerFrozenRaw h raw) := by
  funext k
  rcases k with g | ⟨d, b, v⟩
  · exact ((samplerLongEmbedding (B := B) inactive h).injective.extend_apply
      long (samplerFrozenRaw h raw) (.inl g)).symm
  · by_cases hd : inactive d
    · have hn : ¬ ∃ k, samplerLongEmbedding (G := G) inactive h k = .inr ⟨d, b, v⟩ := by
        intro hk
        exact ((samplerLongEmbedding_dedicated_mem_range inactive h d b v).mp hk) hd
      rw [Function.extend_apply' long (samplerFrozenRaw h raw) _ hn]
      simp only [Function.comp_apply, samplerSeparatedVariable_inactive inactive h d b v hd,
        Sum.elim_inr, samplerFrozenRaw]
    · simp only [Function.comp_apply, samplerSeparatedVariable_active inactive h d b v hd,
        Sum.elim_inl]
      exact ((samplerLongEmbedding (G := G) inactive h).injective.extend_apply
        long (samplerFrozenRaw h raw) (.inr ⟨⟨d, hd⟩, b, v⟩)).symm

theorem eval_rename_samplerSeparatedVariable {R : Type*} [CommRing R]
    (inactive : D → Prop) (h : D → ℕ)
    (P : MvPolynomial (SamplerTupleIndex G B h) R)
    (long : SamplerLongVariables inactive G B h → R)
    (raw : PrincipalTupleIndex B h × Option Empty → R) :
    eval (Sum.elim long raw) (rename (samplerSeparatedVariable inactive h) P) =
      eval long (conditionPolynomial (samplerLongEmbedding inactive h)
        (samplerLongEmbedding inactive h).injective (samplerFrozenRaw h raw) P) := by
  rw [eval_rename, samplerSeparatedValues_eq_extend, eval_conditionPolynomial]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedSeparatedCongruencePolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j)

theorem allocatedUnconditionedCongruenceIntegerPolynomial_condition
    (v : LayerSamplerVariables G I n B → ℤ) :
    conditionPolynomial (allocatedLongEmbedding inactive) (allocatedLongEmbedding inactive).injective v
      (allocatedUnconditionedCongruenceIntegerPolynomial inactive j base noise r projection o) =
      allocatedCongruenceIntegerPolynomial inactive j base noise r projection v o := by
  rcases o with x | i | a <;> rfl

theorem allocatedSeparatedCongruencePolynomial_eval
    (long : LayerSamplerLongVariables inactive G B → ℤ)
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ) :
    MvPolynomial.eval (Sum.elim long raw)
      (allocatedSeparatedCongruencePolynomial inactive j base noise r projection o) =
      MvPolynomial.eval long (allocatedCongruenceIntegerPolynomial inactive j base noise r projection
        (samplerFrozenRaw (layerSamplerDegree I n) raw) o) := by
  rw [allocatedSeparatedCongruencePolynomial, eval_rename_samplerSeparatedVariable]
  rw [← allocatedUnconditionedCongruenceIntegerPolynomial_condition]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedForecastShortRawDependence
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

local instance forecastModulusNeZero_r9d97c1_1 (Pr : Finset ℕ) (A : ℕ → ℕ)
    [∀ p : Pr, NeZero p.val] : NeZero (∏ p : Pr, p.val ^ A p.val) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

theorem allocatedForecastPolynomial_crt_decay_of_bad_product_s2_oai
    (hm : 0 < m) (Pr : Finset ℕ) [∀ p : Pr, NeZero p.val]
    (A e : ℕ → ℕ) (hp : ∀ p ∈ Pr, p.Prime) (C : ℝ) (hC : 0 ≤ C) (Rbad : ℕ)
    (hbad : (∏ p : Pr, p.val ^ allocatedCongruenceBadDepth
      inactive noise r projection spatial kernel block Pr A C p.val) ≤ Rbad)
    (base : X → ℤ)
    (origin : ∀ p : Pr, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val))
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X E inactive) →
      ZMod (∏ p : Pr, p.val ^ A p.val)) ℂ) :
    letI : DecidableEq Pr := Classical.decEq _
    ‖finiteImageCharacteristic
      (crtPolynomialInputLaw (fun p : Pr => p.val) (fun p : Pr => A p.val)
        (fun p : Pr => e p.val)
        (primePower_crt_coprime (fun p : Pr => p.val) (fun p : Pr => A p.val)
          (fun p => hp p.val p.property) Subtype.val_injective) origin)
      (fun t j => (integerLongPolynomialOutput
        (allocatedForecastPolynomial inactive base noise r projection) raw
        (∏ p : Pr, p.val ^ A p.val) t j : ZMod (∏ p : Pr, p.val ^ A p.val))) χ‖ ≤
      ((Rbad * ∏ p : Pr, p.val ^ e p.val : ℕ) : ℝ) ^
        (modularRankDecayExponent m C * modularRankChargeFactor m) *
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent m C) := by
  let : DecidableEq Pr := Classical.decEq _
  have heq := crtPolynomialInputLaw_integerLong_characteristic_of_output
    (fun p : Pr => p.val) (fun p : Pr => A p.val) (fun p : Pr => e p.val)
    (primePower_crt_coprime (fun p : Pr => p.val) (fun p : Pr => A p.val)
      (fun p => hp p.val p.property) Subtype.val_injective) origin
    (allocatedForecastPolynomial inactive base noise r projection) raw
    (crtPrimePowerIntegerPolynomialOutput (fun p : Pr => p.val) (fun p : Pr => A p.val)
      (fun p : Pr => e p.val)
      (primePower_crt_coprime (fun p : Pr => p.val) (fun p : Pr => A p.val)
        (fun p => hp p.val p.property) Subtype.val_injective)
      (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j)
        (samplerFrozenRaw (layerSamplerDegree I n) raw)) origin)
    (fun x j => by
      simpa only [crtPrimePowerIntegerPolynomialOutput, prescribedCRTPolynomialInput,
        allocatedForecastPolynomial] using
        (allocatedSeparatedCongruencePolynomial_eval inactive j.1 base noise r (projection j.1)
          j.2 _ raw).symm) χ
  rw [heq]
  exact allocatedCongruence_crt_rational_decay_of_bad_product
    inactive noise r projection spatial kernel block hm Pr A e hp C hC Rbad hbad base
    (samplerFrozenRaw (layerSamplerDegree I n) raw) origin χ

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedForecastPolynomial_crt_decay_of_bad_product_s2_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedForecastPolynomial_crt_decay_of_bad_product_s2_oai.{u_1, u_2, u_3, u_4, u_5}
