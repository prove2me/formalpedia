-- Prove2me | solution 1 for GlobalTheory.SS.Weight.le_add_of_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:22:30.969867+00:00
-- url     : https://prove2.me/submissions/ce72c15b-2bdd-4d36-b147-2ced8942681b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsNilpotentSubOneOfConjPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankLeOfWeightsUnipotentSymplecticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_WeightLeAddOfTorsionPairing
import Theorems.Thm_GlobalTheory_SS_Weight_finrank_le_of_card
import Theorems.Thm_GlobalTheory_SS_Weight_finrank_le_ker_add
import Theorems.Thm_GlobalTheory_SS_Weight_exists_lift
import Theorems.Thm_GlobalTheory_exists_tateModule_of_card
import Theorems.Thm_GlobalTheory_isNilpotent_sub_one_of_conj_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Weight
open Module
open scoped TensorProduct nonZeroDivisors
namespace GlobalTheory.SS.Weight
theorem _root_.solution (M A : Type) [AddCommGroup M] [AddCommGroup A] (l q g t a c C : ℕ)
    (hl : l.Prime) (hl3 : 3 ≤ l) (hq : 2 ≤ q) (hc : 1 ≤ c)
    (hA : ∀ n, Nat.card {x : A // l ^ n • x = 0} = l ^ n)
    (hM : ∀ n, Nat.card {x : M // l ^ n • x = 0} = l ^ (n * (2 * g)))
    (e : ℕ → M → M → A)
    (he1 : ∀ n x x' y, l ^ n • x = 0 → l ^ n • x' = 0 → l ^ n • y = 0 →
      e n (x + x') y = e n x y + e n x' y ∧ e n y x = - e n x y)
    (he2 : ∀ n x y, l ^ (n + 1) • x = 0 → l ^ n • y = 0 → e (n + 1) x y = e n (l • x) y)
    (he3 : ∀ n x, l ^ n • x = 0 → (∀ y, l ^ n • y = 0 → e n x y = 0) → x = 0)
    (S Φ : M ≃+ M)
    (hSΦ : ∀ n x y, l ^ n • x = 0 → l ^ n • y = 0 →
      e n (S x) (S y) = e n x y ∧ e n (Φ x) (Φ y) = q • e n x y)
    (hcomm : ∀ n x, l ^ n • x = 0 → Φ (S x) = S^[q] (Φ x))
    (hS1 : ∀ x, l • x = 0 → S x = x) (H W : AddSubgroup M) (P : Polynomial ℤ)
    (hH : ∀ n x, l ^ n • x = 0 → S x = x → c • x ∈ H)
    (hcard : ∀ n, Nat.card {x : H // l ^ n • x = 0} ≤ C * l ^ (n * (t + 2 * a)) ∧
      Nat.card {x : W // l ^ n • x = 0} ≤ C * l ^ (n * t))
    (hP : ∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < q)
    (hW : ∀ n, ∀ x ∈ W, l ^ n • x = 0 → Φ x = q • x)
    (hPW : ∀ n, ∀ x ∈ H, l ^ n • x = 0 →
      ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j • (Φ^[j] x) ∈ W) : g ≤ t + a := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨T, _, _, π, _, _, hrk, h1, h0, hs, hsurj, hker, hu⟩ :=
    GlobalTheory.exists_tateModule_of_card M l (2 * g) fun n => by rw [hM, mul_comm]
  obtain ⟨T', _, _, π', _, _, hrk', h1', h0', hs', -, -, hu'⟩ :=
    GlobalTheory.exists_tateModule_of_card A l 1 fun n => by rw [hA, one_mul]
  have hext : ∀ x y : T, (∀ n, π n x = π n y) → x = y := fun x y h =>
    (hu (fun n => π n y) (h0 y) (fun n => h1 n y)).unique h fun _ => rfl
  have hext' : ∀ x y : T', (∀ n, π' n x = π' n y) → x = y := fun x y h =>
    (hu' (fun n => π' n y) (h0' y) (fun n => h1' n y)).unique h fun _ => rfl
  have htor : ∀ n x, l ^ n • π n x = 0 := fun n x => by
    rw [← map_nsmul, hker]; exact ⟨x, rfl⟩
  have hfin : ∀ n, Finite {x : M // l ^ n • x = 0} := fun n =>
    Nat.finite_of_card_ne_zero (by rw [hM]; exact pow_ne_zero _ hl.ne_zero)
  have hsm : ∀ n (k : ℕ) x y, l ^ n • x = 0 → l ^ n • y = 0 →
      e n (k • x) y = k • e n x y := by
    intro n k x y hx hy
    induction k with
    | zero =>
      have := (he1 n 0 0 y (by simp) (by simp) hy).1
      simpa using this
    | succ k ih =>
      rw [succ_nsmul, succ_nsmul, (he1 n _ x y (by rw [smul_comm, hx, smul_zero]) hx hy).1, ih]
  have hsk : ∀ n x y, l ^ n • x = 0 → l ^ n • y = 0 → e n y x = - e n x y :=
    fun n x y hx hy => (he1 n x x y hx hx hy).2
  choose b hb using fun x y : T => (hu' (fun n => e n (π n x) (π n y))
    (by
      have := hsm 0 0 (π 0 x) (π 0 y) (htor _ _) (htor _ _)
      rw [zero_smul, zero_smul] at this
      rw [← this, h0 x])
    (fun n => by
      have hy : l ^ (n + 1) • π n y = 0 := by rw [pow_succ', mul_smul, htor, smul_zero]
      rw [hsk (n + 1) _ _ (htor _ y) (htor _ x), smul_neg, ← hsm _ _ _ _ (htor _ y) (htor _ x),
        h1, ← hsk (n + 1) _ _ hy (htor _ x), he2 _ _ _ (htor _ x) (htor _ y), h1])).exists
  have bsk : ∀ x y, b y x = - b x y := fun x y => hext' _ _ fun n => by
    rw [map_neg, hb, hb, hsk n _ _ (htor _ x) (htor _ y)]
  have badd : ∀ x x' y, b (x + x') y = b x y + b x' y := fun x x' y => hext' _ _ fun n => by
    rw [map_add, hb, hb, hb, map_add, (he1 n _ _ _ (htor _ x) (htor _ x') (htor _ y)).1]
  have bsm : ∀ (r : ℤ_[l]) x y, b (r • x) y = r • b x y := fun r x y => hext' _ _ fun n => by
    rw [hs', hb, hb, hs, hsm n _ _ _ (htor _ x) (htor _ y)]
  let φ : T' ≃ₗ[ℤ_[l]] ℤ_[l] := LinearEquiv.ofFinrankEq T' ℤ_[l] (by rw [hrk', finrank_self])
  let B : LinearMap.BilinForm ℤ_[l] T := LinearMap.mk₂ ℤ_[l] (fun x y => φ (b x y))
    (fun x x' y => by rw [badd, map_add]) (fun r x y => by rw [bsm, map_smul])
    (fun x y y' => by rw [bsk (y + y'), badd, bsk y x, bsk y' x, neg_add, map_add])
    (fun r x y => by rw [bsk (r • y), bsm, bsk y x, ← smul_neg, map_smul])
  have hBb : ∀ x y, B x y = φ (b x y) := fun _ _ => rfl
  obtain ⟨S', hS'⟩ := exists_lift l π h1 h0 hs hu S
  obtain ⟨Φ', hΦ'⟩ := exists_lift l π h1 h0 hs hu Φ
  have hit : ∀ (E : M ≃+ M) (E' : T ≃ₗ[ℤ_[l]] T), (∀ n x, π n (E' x) = E (π n x)) →
      ∀ n (j : ℕ) x, π n (E'^[j] x) = E^[j] (π n x) := by
    intro E E' h n j
    induction j with
    | zero => intro t; rfl
    | succ j ih => intro t; rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, h]
  have hcomm' : Φ' * S' = S' ^ q * Φ' := by
    ext x
    refine hext _ _ fun n => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.pow_apply, hit S S' hS', hΦ',
      hΦ', hS', hcomm n _ (htor n x)]
  have hN := GlobalTheory.isNilpotent_sub_one_of_conj_pow l hl3 T S' Φ' q hq hcomm' fun x => by
    have : π 1 (S' x - x) = 0 := by
      rw [map_sub, hS', hS1 _ (by simpa using htor 1 x), sub_self]
    simpa using (hker 1 _).1 this
  let W' : Submodule ℤ_[l] T :=
    { carrier := {x | ∀ n, π n x ∈ W}
      add_mem' := fun hx hy n => by rw [map_add]; exact W.add_mem (hx n) (hy n)
      zero_mem' := fun n => by rw [map_zero]; exact W.zero_mem
      smul_mem' := fun r x hx n => by rw [hs]; exact W.nsmul_mem (hx n) _ }
  have hfixH : ∀ x, S' x = x → ∀ n, π n (c • x) ∈ H := fun x hx n => by
    rw [map_nsmul]
    exact hH n _ (htor n x) (by rw [← hS', hx])
  have main := finrank_le_ker_add l B ?_ ?_ S' Φ' q hq hN ?_ ?_ hcomm' W' P hP ?_ c (by omega) ?_
  · have hW' : finrank ℤ_[l] W' ≤ t :=
      finrank_le_of_card l π hker hfin W' W (fun n x hx => hx n) C t fun n => (hcard n).2
    have hinj : Function.Injective (c • LinearMap.id : T →ₗ[ℤ_[l]] T) := by
      intro x y h
      have hc0 : (c : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      refine smul_right_injective T hc0 ?_
      simpa [Nat.cast_smul_eq_nsmul] using h
    have hK := finrank_le_of_card l π hker hfin
      ((LinearMap.ker ((S' : T →ₗ[ℤ_[l]] T) - 1)).map (c • LinearMap.id : T →ₗ[ℤ_[l]] T)) H
      (by
        rintro n _ ⟨x, hx, rfl⟩
        exact hfixH x (by simpa [sub_eq_zero] using hx) n) C _ fun n => (hcard n).1
    rw [← (Submodule.equivMapOfInjective _ hinj _).finrank_eq] at hK
    omega
  · intro x hx
    refine hext _ _ fun n => ?_
    rw [map_zero]
    refine he3 n _ (htor n x) fun y hy => ?_
    obtain ⟨y, rfl⟩ := hsurj n y hy
    rw [← hb, (map_eq_zero_iff φ φ.injective).1 (hx y), map_zero]
  · intro x y
    rw [hBb, hBb, bsk, map_neg]
  · intro x y
    rw [hBb, hBb]
    congr 1
    refine hext' _ _ fun n => ?_
    rw [hb, hb, hS', hS', (hSΦ n _ _ (htor n x) (htor n y)).1]
  · intro x y
    rw [hBb, hBb, ← nsmul_eq_mul, ← map_nsmul]
    congr 1
    refine hext' _ _ fun n => ?_
    rw [map_nsmul, hb, hb, hΦ', hΦ', (hSΦ n _ _ (htor n x) (htor n y)).2]
  · intro x hx
    refine hext _ _ fun n => ?_
    rw [hΦ', map_nsmul, hW n _ (hx n) (htor n x)]
  · intro x hx n
    rw [map_sum]
    simp only [map_zsmul, hit Φ Φ' hΦ']
    exact hPW n _ (hfixH x hx n) (htor n _)
end GlobalTheory.SS.Weight
