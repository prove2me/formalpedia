-- Prove2me | solution 1 for ModularCurve.CharPModel.exists_eq_const_mul_of_redHom_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/672cd769-4a42-53e9-8ce9-8bdc49add02a

import Mathlib.FieldTheory.Relrank
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_exists_eq_const_mul_of_redHom_eq_zero

set_option autoImplicit false

noncomputable section

open Polynomial

namespace CharpS10bB

namespace SD2r

open IsLocalRing IntermediateField

section Scaling

variable {A : Type*} [CommRing A] [IsDomain A] [ValuationRing A]

theorem exists_dvd_forall {ι : Type*} (c : ι → A) (s : Finset ι) (hs : s.Nonempty) :
    ∃ i ∈ s, ∀ j ∈ s, c i ∣ c j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · refine ⟨a, Finset.mem_insert_self _ _, fun j hj => ?_⟩
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact dvd_rfl
      · exact absurd hj (Finset.notMem_empty _)
    · obtain ⟨i, hi, hmin⟩ := ih hne
      rcases ValuationRing.dvd_total (c a) (c i) with h | h
      · refine ⟨a, Finset.mem_insert_self _ _, fun j hj => ?_⟩
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact dvd_rfl
        · exact h.trans (hmin j hj)
      · refine ⟨i, Finset.mem_insert_of_mem hi, fun j hj => ?_⟩
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact h
        · exact hmin j hj

variable {R : Type*} [CommRing R] (𝔭 : Ideal R) (φ : A →+* R) {ι : Type*} (b : ι → R)

def IndepModPrime : Prop :=
  ∀ (s : Finset ι) (c : ι → A), (∑ i ∈ s, φ (c i) * b i) ∈ 𝔭 → ∀ i ∈ s, c i ∈ maximalIdeal A

theorem exists_eq_mul_notMem
    (hspan : ∀ r : R, ∃ (s : Finset ι) (c : ι → A), r = ∑ i ∈ s, φ (c i) * b i)
    (hind : IndepModPrime 𝔭 φ b) {r : R} (hr : r ≠ 0) :
    ∃ (c : A) (r' : R), r' ∉ 𝔭 ∧ r = φ c * r' := by
  classical
  obtain ⟨s, c, rfl⟩ := hspan r

  set s' := s.filter (fun i => c i ≠ 0) with hs'
  have hsum : ∑ i ∈ s, φ (c i) * b i = ∑ i ∈ s', φ (c i) * b i := by
    rw [hs', Finset.sum_filter_of_ne]
    intro i _ hne hci
    apply hne
    rw [hci, map_zero, zero_mul]
  have hne : s'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    apply hr
    rw [hsum, he, Finset.sum_empty]
  obtain ⟨i₀, hi₀, hmin⟩ := exists_dvd_forall c s' hne
  have hci₀ : c i₀ ≠ 0 := (Finset.mem_filter.mp hi₀).2
  choose! d hd using hmin
  refine ⟨c i₀, ∑ j ∈ s', φ (d j) * b j, ?_, ?_⟩
  · intro hmem
    have h1 : d i₀ ∈ maximalIdeal A := hind s' d hmem i₀ hi₀
    have hd1 : d i₀ = 1 := by
      apply mul_left_cancel₀ hci₀
      rw [mul_one]
      exact (hd i₀ hi₀).symm
    rw [hd1] at h1
    exact (maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  · rw [hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hd j hj, map_mul, mul_assoc]

end Scaling

section H1

variable {A : Type*} [CommRing A] [IsLocalRing A]
variable {R : Type*} [CommRing R] {k : Type*} [Field k] {S : Type*} [CommRing S] [Algebra k S]
variable (φ : A →+* R) (red : A →+* k) (red₀ : R →+* S)

theorem mem_maximalIdeal_of_map_eq_zero {a : A} (ha : red a = 0) : a ∈ maximalIdeal A := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact (hu.map red).ne_zero ha

theorem indepModKer_of_linearIndependent {ι : Type*} (b : ι → R)
    (hcompat : ∀ a, red₀ (φ a) = algebraMap k S (red a))
    (hli : LinearIndependent k (fun i => red₀ (b i))) :
    ∀ (s : Finset ι) (c : ι → A), (∑ i ∈ s, φ (c i) * b i) ∈ RingHom.ker red₀ →
      ∀ i ∈ s, c i ∈ maximalIdeal A := by
  intro s c hmem i hi
  apply mem_maximalIdeal_of_map_eq_zero red
  rw [RingHom.mem_ker, map_sum] at hmem
  have hsum : ∑ j ∈ s, red (c j) • red₀ (b j) = 0 := by
    rw [← hmem]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hcompat, Algebra.smul_def]
  exact linearIndependent_iff'.mp hli s (fun j => red (c j)) hsum i hi

end H1

section H2

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

theorem linearIndependent_pow_of_transcendental {x : E} (hx : Transcendental k x) :
    LinearIndependent k (fun a : ℕ => x ^ a) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hinj := transcendental_iff_injective.mp hx
  set p : Polynomial k := ∑ a ∈ s, Polynomial.monomial a (g a) with hp
  have hp0 : Polynomial.aeval x p = 0 := by
    rw [hp, map_sum, ← hsum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Polynomial.aeval_monomial, Algebra.smul_def]
  have hpz : p = 0 := hinj (by rw [hp0, map_zero])
  have hc : p.coeff i = g i := by
    rw [hp, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' s i g, if_pos hi]
  rw [hpz, Polynomial.coeff_zero] at hc
  exact hc.symm

theorem linearIndependent_pow_fin_of_relfinrank (x y : E) {n : ℕ} (hn : 0 < n)
    (hdeg : relfinrank k⟮x⟯ (adjoin k {x, y}) = n) :
    LinearIndependent k⟮x⟯ (fun i : Fin n => y ^ (i : ℕ)) := by
  have hle : k⟮x⟯ ≤ adjoin k {x, y} := adjoin.mono k _ _ (by simp)
  have hKy : extendScalars hle = k⟮x⟯⟮y⟯ := by
    rw [extendScalars_adjoin hle]
    apply le_antisymm
    · rw [adjoin_le_iff]
      intro z hz
      rcases hz with rfl | hz
      · have := IntermediateField.algebraMap_mem k⟮z⟯⟮y⟯ (AdjoinSimple.gen k z)
        rwa [AdjoinSimple.algebraMap_gen] at this
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact mem_adjoin_simple_self _ z
    · exact adjoin.mono _ _ _ (by simp)
  have hfin : Module.finrank k⟮x⟯ k⟮x⟯⟮y⟯ = n := by
    rw [← hdeg, relfinrank_eq_finrank_of_le hle, hKy]
  haveI : FiniteDimensional k⟮x⟯ k⟮x⟯⟮y⟯ := Module.finite_of_finrank_pos (by omega)
  have hint : IsIntegral k⟮x⟯ y := by
    have h1 : IsIntegral k⟮x⟯ (AdjoinSimple.gen k⟮x⟯ y) := Algebra.IsIntegral.isIntegral _
    have h2 := isIntegral_iff.mp h1
    rwa [AdjoinSimple.coe_gen] at h2
  have hnat : (minpoly k⟮x⟯ y).natDegree = n := by
    rw [← adjoin.finrank hint, hfin]
  set pb := adjoin.powerBasis hint with hpb
  have hdim : pb.dim = n := by rw [hpb, adjoin.powerBasis_dim, hnat]
  have hli : LinearIndependent k⟮x⟯ (fun i : Fin pb.dim => y ^ (i : ℕ)) := by
    have h0 : LinearIndependent k⟮x⟯ pb.basis := pb.basis.linearIndependent
    have h1 := h0.map' (k⟮x⟯⟮y⟯.val).toLinearMap
      (LinearMap.ker_eq_bot.mpr (k⟮x⟯⟮y⟯.val).toRingHom.injective)
    convert h1 using 1
    · ext i
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply, PowerBasis.basis_eq_pow, hpb,
        adjoin.powerBasis_gen, map_pow]
      rfl
    all_goals rfl
  subst hdim
  exact hli

theorem linearIndependent_monomial_of_relfinrank (x y : E) {n : ℕ} (hn : 0 < n)
    (hx : Transcendental k x) (hdeg : relfinrank k⟮x⟯ (adjoin k {x, y}) = n) :
    LinearIndependent k (fun p : ℕ × Fin n => x ^ p.1 * y ^ (p.2 : ℕ)) := by
  have hb : LinearIndependent k (fun a : ℕ => (AdjoinSimple.gen k x) ^ a) := by
    apply LinearIndependent.of_comp (k⟮x⟯.val).toLinearMap
    convert linearIndependent_pow_of_transcendental hx using 1
    all_goals rfl
  have hc := linearIndependent_pow_fin_of_relfinrank x y hn hdeg
  convert linearIndependent_smul hb hc using 1
  all_goals rfl

end H2

section Dock

variable {A : Type*} [CommRing A] [IsLocalRing A]
variable {R : Type*} [CommRing R] {k E : Type*} [Field k] [Field E] [Algebra k E]
variable (φ : A →+* R) (red : A →+* k) (red₀ : R →+* E)

theorem indepModKer_monomial (hcompat : ∀ a, red₀ (φ a) = algebraMap k E (red a))
    (X Y : R) {n : ℕ} (hn : 0 < n) (hx : Transcendental k (red₀ X))
    (hdeg : relfinrank k⟮red₀ X⟯ (adjoin k {red₀ X, red₀ Y}) = n) :
    ∀ (s : Finset (ℕ × Fin n)) (c : ℕ × Fin n → A),
      (∑ p ∈ s, φ (c p) * (X ^ p.1 * Y ^ (p.2 : ℕ))) ∈ RingHom.ker red₀ →
        ∀ p ∈ s, c p ∈ maximalIdeal A := by
  apply indepModKer_of_linearIndependent φ red red₀ (fun p : ℕ × Fin n => X ^ p.1 * Y ^ (p.2 : ℕ))
    hcompat
  convert linearIndependent_monomial_of_relfinrank (red₀ X) (red₀ Y) hn hx hdeg using 1
  ext p
  simp only [map_mul, map_pow]

end Dock

theorem exists_sum_monomial_of_mem_closure {A E : Type*} [CommRing A] [CommRing E]
    (φ : A →+* E) (X Y : E) {P : Polynomial (Polynomial A)} (hP : P.Monic)
    (hrel : P.eval₂ (Polynomial.eval₂RingHom φ X) Y = 0)
    {r : E} (hr : r ∈ Subring.closure (Set.range φ ∪ {X, Y})) :
    ∃ (s : Finset (ℕ × Fin P.natDegree)) (c : ℕ × Fin P.natDegree → A),
      r = ∑ p ∈ s, φ (c p) * (X ^ p.1 * Y ^ (p.2 : ℕ)) := by
  classical
  set f : Polynomial A →+* E := Polynomial.eval₂RingHom φ X with hf
  set Ψ : Polynomial (Polynomial A) →+* E := Polynomial.eval₂RingHom f Y with hΨ

  have hle : Subring.closure (Set.range φ ∪ {X, Y}) ≤ Ψ.range := by
    rw [Subring.closure_le]
    rintro z (⟨a, rfl⟩ | hz)
    · exact ⟨Polynomial.C (Polynomial.C a), by simp [hΨ, hf]⟩
    · rcases hz with rfl | hz
      · exact ⟨Polynomial.C Polynomial.X, by simp [hΨ, hf]⟩
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact ⟨Polynomial.X, by simp [hΨ]⟩
  obtain ⟨G, rfl⟩ := hle hr
  by_cases hP1 : P = 1
  ·
    have h10 : (1 : E) = 0 := by
      have : Ψ P = 0 := hrel
      rwa [hP1, map_one] at this
    refine ⟨∅, fun _ => 0, ?_⟩
    rw [Finset.sum_empty, ← mul_one (Ψ G), h10, mul_zero]
  have hΨP : Ψ P = 0 := hrel
  set Rm := G %ₘ P with hRm
  have hG : Ψ G = Ψ Rm := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div G P]
    rw [map_add, map_mul, hΨP, zero_mul, add_zero]
  have hdeg : Rm.natDegree < P.natDegree := Polynomial.natDegree_modByMonic_lt G hP hP1
  set n := P.natDegree with hn
  set D := (Finset.range n).sup (fun i => (Rm.coeff i).natDegree) + 1 with hD
  have hDi : ∀ i ∈ Finset.range n, (Rm.coeff i).natDegree < D := fun i hi =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (Rm.coeff i).natDegree) hi)
  refine ⟨(Finset.range D) ×ˢ (Finset.univ : Finset (Fin n)),
    fun p => (Rm.coeff (p.2 : ℕ)).coeff p.1, ?_⟩
  rw [hG, Finset.sum_product, Finset.sum_comm]
  rw [show Ψ Rm = Rm.eval₂ f Y from rfl, Polynomial.eval₂_eq_sum_range' f hdeg Y,
    ← Fin.sum_univ_eq_sum_range (fun i => f (Rm.coeff i) * Y ^ i) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show f (Rm.coeff i) = (Rm.coeff i).eval₂ φ X from rfl,
    Polynomial.eval₂_eq_sum_range' φ (hDi i (by simp)) X, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end SD2r

end CharpS10bB

end

theorem solution
    {A : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    {k : Type*} [Field k] (red : A →+* k)
    {E : Type*} [CommRing E] (φ : A →+* E) (X Y : E)
    (P : Polynomial (Polynomial A)) (hP : P.Monic) (hn : 0 < P.natDegree)
    (hrel : P.eval₂ (Polynomial.eval₂RingHom φ X) Y = 0)
    (R : Subring E) (hφ : ∀ a : A, φ a ∈ R) (hXR : X ∈ R) (hYR : Y ∈ R)
    (hRle : R ≤ Subring.closure (Set.range φ ∪ {X, Y}))
    {S : Type*} [Field S] [Algebra k S] (red₀ : R →+* S)
    (hcompat : ∀ a : A, red₀ ⟨φ a, hφ a⟩ = algebraMap k S (red a))
    (hX : Transcendental k (red₀ ⟨X, hXR⟩))
    (hdeg : (IntermediateField.adjoin k {red₀ ⟨X, hXR⟩}).relfinrank
      (IntermediateField.adjoin k {red₀ ⟨X, hXR⟩, red₀ ⟨Y, hYR⟩}) = P.natDegree)
    (r : R) (hr : red₀ r = 0) :
    ∃ m : A, red m = 0 ∧ ∃ r' : R, r = ⟨φ m, hφ m⟩ * r' := by
  classical
  let φR : A →+* R := φ.codRestrict R hφ
  have hspan : ∀ r : R, ∃ (s : Finset (ℕ × Fin P.natDegree)) (c : ℕ × Fin P.natDegree → A),
      r = ∑ p ∈ s, φR (c p) * ((⟨X, hXR⟩ : R) ^ p.1 * (⟨Y, hYR⟩ : R) ^ (p.2 : ℕ)) := by
    intro r
    obtain ⟨s, c, hc⟩ := CharpS10bB.SD2r.exists_sum_monomial_of_mem_closure φ X Y hP hrel (hRle r.2)
    refine ⟨s, c, R.subtype_injective ?_⟩
    rw [map_sum]
    simp_rw [map_mul, map_pow]
    exact hc
  have hind : CharpS10bB.SD2r.IndepModPrime (RingHom.ker red₀) φR
      (fun p : ℕ × Fin P.natDegree => (⟨X, hXR⟩ : R) ^ p.1 * (⟨Y, hYR⟩ : R) ^ (p.2 : ℕ)) := by
    intro s c hmem
    exact CharpS10bB.SD2r.indepModKer_monomial φR red red₀ hcompat ⟨X, hXR⟩ ⟨Y, hYR⟩ hn hX hdeg
      s c hmem
  by_cases hz : r = 0
  · exact ⟨0, by rw [map_zero], 0, by rw [hz, mul_zero]⟩
  obtain ⟨c, r', hr', hrc⟩ := CharpS10bB.SD2r.exists_eq_mul_notMem _ φR _ hspan hind hz
  refine ⟨c, ?_, r', hrc⟩
  have h1 : red₀ r = 0 := hr
  rw [hrc, map_mul, show red₀ (φR c) = algebraMap k S (red c) from hcompat c] at h1
  have h2 := (mul_eq_zero.1 h1).resolve_right (fun h => hr' (RingHom.mem_ker.2 h))
  exact (algebraMap k S).injective (by rw [h2, map_zero])

end S_ModularCurve_CharPModel_exists_eq_const_mul_of_redHom_eq_zero
end P2MW
export P2MW.S_ModularCurve_CharPModel_exists_eq_const_mul_of_redHom_eq_zero (solution)
