-- Prove2me | solution 1 for GottschalkSurjunctivity.gottschalk_surjunctivity_conjecture
-- status  : ACCEPTED   (disprove)
-- author  : @dbenbenn
-- created : 2026-10-07T15:11:41.521471+00:00
-- url     : https://prove2.me/submissions/3da8f449-c464-4020-aceb-3106c8ad97d9

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs
set_option linter.all false
universe portUniverse1 contextUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5 portUniverse6 portUniverse7 portUniverse8 portUniverse9 u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 contextUniverse2 portUniverse10 portUniverse11 portUniverse12 portUniverse13 portUniverse14 portUniverse15 portUniverse16 portUniverse17 portUniverse18 portUniverse19 portUniverse20 portUniverse21 portUniverse22 portUniverse23 portUniverse24 portUniverse25 portUniverse26 portUniverse27 portUniverse28 portUniverse29 portUniverse30 portUniverse31 portUniverse32 portUniverse33 portUniverse34 portUniverse35 portUniverse36 portUniverse37 portUniverse38 portUniverse39 portUniverse40 portUniverse41 portUniverse42 portUniverse43 portUniverse44 portUniverse45 portUniverse46 portUniverse47 portUniverse48 portUniverse49 portUniverse50 portUniverse51 portUniverse52 portUniverse53 portUniverse54 portUniverse55 portUniverse56 portUniverse57 portUniverse58 portUniverse59 portUniverse60 portUniverse61 portUniverse62 portUniverse63 portUniverse64 portUniverse65 portUniverse66 portUniverse67 portUniverse68 portUniverse69 portUniverse70 portUniverse71 portUniverse72 portUniverse73 portUniverse74 portUniverse75 portUniverse76 u v contextUniverse3 contextUniverse4 contextUniverse5 contextUniverse6

section
namespace OAI

section
namespace OddKaplansky

@[irreducible] noncomputable def sourceM : ℕ := Nat.choose 1200 600
@[irreducible] noncomputable def sourcePrime : ℕ := Nat.minFac ((Nat.factorial sourceM)^2 + 1)

lemma sourceM_large : 1200 ≤ sourceM := by
  have h := Nat.choose_le_middle 1 1200
  rw [Nat.choose_one_right, show 1200 / 2 = 600 from rfl] at h
  unfold sourceM
  exact h

lemma sourcePrime_prime : sourcePrime.Prime := by
  unfold sourcePrime
  apply Nat.minFac_prime
  have := Nat.factorial_pos sourceM
  have := pow_pos this 2
  omega

lemma sourcePrime_dvd : sourcePrime ∣ (Nat.factorial sourceM)^2 + 1 :=
  by unfold sourcePrime; exact Nat.minFac_dvd _

lemma sourcePrime_gt : sourceM < sourcePrime := by
  by_contra h
  have hd := Nat.dvd_factorial sourcePrime_prime.pos (Nat.le_of_not_gt h)
  have hsq : sourcePrime ∣ (Nat.factorial sourceM)^2 :=
    dvd_pow hd (by decide : 2 ≠ 0)
  have : sourcePrime ∣ 1 := (Nat.dvd_add_iff_right hsq).mpr sourcePrime_dvd
  exact sourcePrime_prime.not_dvd_one this

lemma sourcePrime_odd : Odd sourcePrime :=
  sourcePrime_prime.odd_of_ne_two (by have := sourcePrime_gt; have := sourceM_large; omega)

instance sourcePrime_fact : Fact sourcePrime.Prime := ⟨sourcePrime_prime⟩

lemma neg_one_isSquare_of_dvd (p n : ℕ) [Fact p.Prime] (h : p ∣ n^2+1) :
    IsSquare (-1 : ZMod p) := by
  refine ⟨(n : ZMod p), ?_⟩
  have hz : (((n^2+1 : ℕ) : ZMod p)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr h
  push_cast at hz
  linear_combination -hz

end OddKaplansky

end

end OAI
end

section
namespace OAI


section
noncomputable section
open scoped Classical
open Polynomial
namespace OddKaplansky.QuadraticTower

variable {F : Type portUniverse1} [Field F]

def polynomial (a : F) : F[X] := X^2 - C a

lemma polynomial_monic (a : F) : (polynomial a).Monic :=
  monic_X_pow_sub_C a (by decide : 2 ≠ 0)

lemma polynomial_degree (a : F) : (polynomial a).natDegree = 2 :=
  natDegree_X_pow_sub_C

lemma polynomial_irreducible {a : F} (ha : ¬ IsSquare a) :
    Irreducible (polynomial a) := by
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro b hb
  exact ha ⟨b, by simpa only [pow_two] using hb.symm⟩

def basis (a : F) : PowerBasis F (AdjoinRoot (polynomial a)) :=
  AdjoinRoot.powerBasis (polynomial_monic a).ne_zero

lemma basis_dim (a : F) : (basis a).dim = 2 := polynomial_degree a
lemma basis_gen (a : F) : (basis a).gen = AdjoinRoot.root (polynomial a) := rfl

instance finiteDimensional (a : F) : FiniteDimensional F (AdjoinRoot (polynomial a)) :=
  (basis a).finite

lemma finrank (a : F) : Module.finrank F (AdjoinRoot (polynomial a)) = 2 := by
  rw [(basis a).finrank, basis_dim]

lemma norm_root (a : F) :
    Algebra.norm F (AdjoinRoot.root (polynomial a)) = -a := by
  rw [← basis_gen a, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, basis_dim]
  have hm := AdjoinRoot.minpoly_powerBasis_gen_of_monic (polynomial_monic a)
  change minpoly F (basis a).gen = polynomial a at hm
  rw [hm]
  simp only [even_two, Even.neg_pow, one_pow, polynomial, coeff_sub, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte, coeff_C_zero, zero_sub, mul_neg, one_mul]

lemma root_not_isSquare {a : F} (ha : ¬ IsSquare a) (hminus : IsSquare (-1 : F)) :
    ¬ IsSquare (AdjoinRoot.root (polynomial a)) := by
  intro hr
  have hn : IsSquare (-a) := by
    rw [← norm_root a]
    exact hr.map (Algebra.norm F)
  exact ha (by simpa only [neg_one_mul, neg_neg] using hminus.mul hn)

instance finite [Finite F] (a : F) : Finite (AdjoinRoot (polynomial a)) :=
  Module.finite_of_finite F

lemma card [Fintype F] (a : F) [Fintype (AdjoinRoot (polynomial a))] :
    Fintype.card (AdjoinRoot (polynomial a)) = (Fintype.card F)^2 := by
  rw [Module.card_eq_pow_finrank (K := F), finrank]

section PrimeField
variable (p : ℕ) [Fact p.Prime]

lemma exists_nonsquare_representative (hp : p ≠ 2) :
    ∃ n : ℕ, n < p ∧ ¬ IsSquare (n : ZMod p) := by
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rw [ringChar.eq (ZMod p) p]; exact hp)
  exact ⟨a.val, a.val_lt, by simpa only [ZMod.natCast_val, ZMod.cast_id', id_eq] using ha⟩

def nonsquareIndex (hp : p ≠ 2) : ℕ := Nat.find (exists_nonsquare_representative p hp)
def eta (hp : p ≠ 2) : ZMod p := (nonsquareIndex p hp : ZMod p)

lemma eta_not_isSquare (hp : p ≠ 2) : ¬ IsSquare (eta p hp) :=
  (Nat.find_spec (exists_nonsquare_representative p hp)).2

abbrev FirstField (hp : p ≠ 2) := AdjoinRoot (polynomial (eta p hp))
instance first_irreducible (hp : p ≠ 2) : Fact (Irreducible (polynomial (eta p hp))) :=
  ⟨polynomial_irreducible (eta_not_isSquare p hp)⟩
instance first_fintype (hp : p ≠ 2) : Fintype (FirstField p hp) := Fintype.ofFinite _

def xi (hp : p ≠ 2) : FirstField p hp := AdjoinRoot.root (polynomial (eta p hp))

abbrev CoeffField (hp : p ≠ 2) := AdjoinRoot (polynomial (xi p hp))
theorem second_irreducible (hp : p ≠ 2) (hminus : IsSquare (-1 : ZMod p)) :
    Irreducible (polynomial (xi p hp)) :=
  polynomial_irreducible (root_not_isSquare (eta_not_isSquare p hp) hminus)

@[instance_reducible]
def coeffField (hp : p ≠ 2) (hminus : IsSquare (-1 : ZMod p)) : Field (CoeffField p hp) := by
  letI : Fact (Irreducible (polynomial (xi p hp))) := ⟨second_irreducible p hp hminus⟩
  infer_instance
instance tower_fintype (hp : p ≠ 2) : Fintype (CoeffField p hp) := Fintype.ofFinite _

lemma first_card (hp : p ≠ 2) : Fintype.card (FirstField p hp) = p^2 := by
  rw [card, ZMod.card]
lemma tower_card (hp : p ≠ 2) : Fintype.card (CoeffField p hp) = p^4 := by
  rw [card, first_card, ← pow_mul]

end PrimeField
end OddKaplansky.QuadraticTower

end
end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.FiniteChoice
noncomputable section
open scoped Classical
variable {A : Type portUniverse1} {B : Type portUniverse2}
def orderedIndex (A : Type portUniverse3) [LinearOrder A] [Fintype A] : A ≃ Fin (Fintype.card A) :=
  (Fintype.orderIsoFinOfCardEq A rfl).symm.toEquiv
def table [LinearOrder A] [Fintype A] (f : A → B) : List B :=
  List.ofFn (fun i => f ((orderedIndex A).symm i))
lemma table_injective [LinearOrder A] [Fintype A] : Function.Injective (table (A := A) (B := B)) := by
  intro f g he
  have hh := List.ofFn_injective he
  funext a
  simpa only [Equiv.symm_apply_apply] using congrFun hh (orderedIndex A a)
@[instance_reducible]
def functionOrder (A : Type portUniverse4) (B : Type portUniverse5) [Fintype A] [LinearOrder A] [LinearOrder B] : LinearOrder (A → B) :=
  LinearOrder.lift' table table_injective
@[instance_reducible]
def tupleOrder (A : Type portUniverse6) (B : Type portUniverse7) [LinearOrder A] [LinearOrder B] : LinearOrder (A×B) :=
  LinearOrder.lift' (fun a : A×B => toLex a) (fun _ _ h => h)
@[instance_reducible]
def residueOrder (n : ℕ) [NeZero n] : LinearOrder (ZMod n) :=
  LinearOrder.lift' ZMod.val (ZMod.val_injective n)
@[instance_reducible]
def multiplicativeOrder [LinearOrder A] : LinearOrder (Multiplicative A) :=
  LinearOrder.lift' Multiplicative.toAdd Multiplicative.toAdd.injective
lemma exists_primitive (F : Type portUniverse8) [Field F] [Fintype F] : ∃ ζ : F, IsPrimitiveRoot ζ (Fintype.card F-1) := by
  obtain ⟨u,hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  refine ⟨u,?_⟩
  rw [← Fintype.card_units F,← Nat.card_eq_fintype_card,← hu]
  simpa only [orderOf_units] using IsPrimitiveRoot.orderOf (u : F)
variable [Fintype A] [sectionInstance1 : LinearOrder A] (P : A → Prop) (hP : ∃ a, P a)
def candidates : Finset A := Finset.univ.filter P
lemma candidates_nonempty
    {A : Type contextUniverse1}
    [Fintype.{contextUniverse1} A]
    [LinearOrder.{contextUniverse1} A]
    (P : A → Prop)
    (hP : @Exists.{contextUniverse1 + 1} A fun a => P a) : (candidates P).Nonempty := by
  obtain ⟨a,ha⟩ := hP
  exact ⟨a,by simp only [candidates, Finset.mem_filter, Finset.mem_univ, ha, and_self]⟩
def first : A := (candidates P).min' (candidates_nonempty P hP)
lemma first_spec : P (first P hP) := by
  have h := Finset.min'_mem (candidates P) (candidates_nonempty P hP)
  simpa only [first,candidates,Finset.mem_filter,Finset.mem_univ,true_and] using h
variable (F : Type portUniverse9) [Field F] [Fintype F] [LinearOrder F]
def primitive : F := first (fun ζ : F => IsPrimitiveRoot ζ (Fintype.card F-1)) (exists_primitive F)
lemma primitive_spec : IsPrimitiveRoot (primitive F) (Fintype.card F-1) := by unfold primitive; exact first_spec (fun ζ : F => IsPrimitiveRoot ζ (Fintype.card F-1)) (exists_primitive F)

end
end OddKaplansky.FiniteChoice

end

end OAI
end

section
namespace OAI

section
namespace OddKaplansky.QuadraticTower
noncomputable section
open scoped Classical
variable (p : ℕ) [Fact p.Prime] (hp : p≠2)
def firstCoordinates : FirstField p hp ≃ₗ[ZMod p] (Fin 2 → ZMod p) :=
  ((basis (eta p hp)).basis.reindex (finCongr (basis_dim (eta p hp)))).equivFun
def secondCoordinates : CoeffField p hp ≃ₗ[FirstField p hp] (Fin 2 → FirstField p hp) :=
  ((basis (xi p hp)).basis.reindex (finCongr (basis_dim (xi p hp)))).equivFun

def coefficientTuple (z : CoeffField p hp) : Fin 4 → ZMod p :=
  ![firstCoordinates p hp (secondCoordinates p hp z 0) 0,
    firstCoordinates p hp (secondCoordinates p hp z 0) 1,
    firstCoordinates p hp (secondCoordinates p hp z 1) 0,
    firstCoordinates p hp (secondCoordinates p hp z 1) 1]
lemma coefficientTuple_injective : Function.Injective (coefficientTuple p hp) := by
  intro a b he
  apply (secondCoordinates p hp).injective
  funext i
  apply (firstCoordinates p hp).injective
  funext j
  fin_cases i <;> fin_cases j
  · exact congrFun he 0
  · exact congrFun he 1
  · exact congrFun he 2
  · exact congrFun he 3
@[instance_reducible]
def fieldOrder : LinearOrder (CoeffField p hp) :=
  @LinearOrder.lift' _ _ (@FiniteChoice.functionOrder (Fin 4) (ZMod p) inferInstance inferInstance (FiniteChoice.residueOrder p))
    (coefficientTuple p hp) (coefficientTuple_injective p hp)
end
end OddKaplansky.QuadraticTower

end

end OAI
end

section
namespace OAI

namespace KaplanskyCounterexample

end KaplanskyCounterexample

end OAI
end

section
namespace OAI

end OAI
end

section
namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry

def sourceQ : ℕ := 2^217

local instance : DecidablePred (fun p : ℕ => p.Prime ∧ sourceQ^100 ∣ p+1) := Classical.decPred _

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

def Qcard (h : ℕ) : ℕ := 2^h

lemma prime_exists (h : ℕ) : ∃ p : ℕ, p.Prime ∧ (Qcard h)^100 ∣ p+1 := by
  have hq : (Qcard h)^100 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by decide : 2 ≠ 0))
  let : NeZero ((Qcard h)^100) := ⟨hq⟩
  obtain ⟨p,_,hp,he⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    ((isUnit_one : IsUnit (1 : ZMod ((Qcard h)^100))).neg) 0
  refine ⟨p,hp,?_⟩
  apply (ZMod.natCast_eq_zero_iff (p+1) ((Qcard h)^100)).mp
  simp only [Nat.cast_add,Nat.cast_one,he,neg_add_cancel]

local instance (h : ℕ) : DecidablePred (fun p : ℕ => p.Prime ∧ (Qcard h)^100 ∣ p+1) :=
  Classical.decPred _

def prime (h : ℕ) : ℕ := Nat.find (prime_exists h)
lemma prime_congruent (h : ℕ) : (Qcard h)^100 ∣ prime h+1 :=
  (Nat.find_spec (prime_exists h)).2
lemma prime_ge (h : ℕ) (hh : 2 ≤ h) : 3 ≤ prime h := by
  have hq : 4 ≤ Qcard h := by exact Nat.pow_le_pow_right (by decide : 0 < 2) hh
  have hpow : Qcard h ≤ (Qcard h)^100 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by omega : 1 ≤ Qcard h) (by decide : 1 ≤ 100)
  have hl : Qcard h ≤ prime h+1 := hpow.trans
    (Nat.le_of_dvd (by omega) (prime_congruent h))
  omega

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

/-- First successful element of a finite, linearly ordered search space. -/
def first {α : Type u_1} [Fintype α] [LinearOrder α] (P : α → Prop) (h : ∃ x, P x) : α :=
  (Finset.univ.filter P).min' (by simpa only [Finset.Nonempty, Finset.mem_filter, Finset.mem_univ, true_and] using h)

lemma first_spec {α : Type u_2} [Fintype α] [LinearOrder α] (P : α → Prop) (h : ∃ x, P x) :
    P (first P h) := by
  have hh := Finset.min'_mem (Finset.univ.filter P) (by simpa only [Finset.Nonempty, Finset.mem_filter, Finset.mem_univ, true_and] using h)
  exact (Finset.mem_filter.mp hh).2

/-- Lexicographic order on coefficient/coordinate vectors, increasing index first. -/
@[instance_reducible] def vectorOrder {ι : Type u_4} [LinearOrder ι] [WellFoundedLT ι]
    {α : Type u_5} [LinearOrder α] : LinearOrder (ι → α) :=
  LinearOrder.lift' (toLex : (ι → α) → Lex (ι → α)) (fun _ _ h => h)

@[instance_reducible] def subsetOrder (α : Type u_6) [Fintype α] [LinearOrder α] : LinearOrder (Finset α) :=
  @LinearOrder.lift' (Finset α) (Lex (α → Bool)) inferInstance
    (fun S => toLex (fun x => decide (x ∈ S))) (by
      intro S T h
      apply Finset.ext
      intro x
      have hx := congrFun (congrArg ofLex h) x
      simpa only [Pi.ofLex_apply, Pi.toLex_apply, decide_eq_true_eq, eq_iff_iff] using congrArg (fun b => b=true) hx)

/-- Residues are ordered 0,...,p-1, independently of their field operations. -/
@[instance_reducible] def residueOrder (p : ℕ) [NeZero p] : LinearOrder (ZMod p) :=
  LinearOrder.lift' ZMod.val (ZMod.val_injective p)

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
namespace OAI

noncomputable section
open scoped Classical
open Polynomial Module
namespace KaplanskyCounterexample.Prescription

local instance two_neZero : NeZero (2 : ℕ) := inferInstance

local instance polynomialResidueOrder : LinearOrder (ZMod 2) := @residueOrder 2 two_neZero
local instance polynomialVectorOrder (d : ℕ) : LinearOrder (Fin (d+1) → ZMod 2) := vectorOrder

def irreducibleCoeffs (d : ℕ) (c : Fin (d+1) → ZMod 2) : Prop :=
  (ofFn (d+1) c).Monic ∧ (ofFn (d+1) c).natDegree=d ∧ Irreducible (ofFn (d+1) c)

lemma irreducibleCoeffs_exists (d : ℕ) (hd : 0 < d) : ∃ c, irreducibleCoeffs d c := by
  let K := GaloisField 2 d
  let b := Field.powerBasisOfFiniteOfSeparable (ZMod 2) K
  have hb : b.dim=d := b.finrank.symm.trans (GaloisField.finrank 2 (Nat.ne_of_gt hd))
  have hi := b.isIntegral_gen
  have hdeg : (minpoly (ZMod 2) b.gen).natDegree=d := b.natDegree_minpoly.trans hb
  refine ⟨toFn (d+1) (minpoly (ZMod 2) b.gen),?_⟩
  unfold irreducibleCoeffs
  rw [ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega : (minpoly (ZMod 2) b.gen).natDegree < d+1)]
  exact ⟨minpoly.monic hi,hdeg,minpoly.irreducible hi⟩

def firstCoeffs (d : ℕ) (hd : 0 < d) : Fin (d+1) → ZMod 2 :=
  first (irreducibleCoeffs d) (irreducibleCoeffs_exists d hd)

def firstPolynomial (d : ℕ) (hd : 0 < d) : (ZMod 2)[X] := ofFn (d+1) (firstCoeffs d hd)

lemma firstPolynomial_monic (d : ℕ) (hd : 0 < d) : (firstPolynomial d hd).Monic :=
  (first_spec _ (irreducibleCoeffs_exists d hd)).1
lemma firstPolynomial_irreducible (d : ℕ) (hd : 0 < d) : Irreducible (firstPolynomial d hd) :=
  (first_spec _ (irreducibleCoeffs_exists d hd)).2.2

/-- Exactly F₂[Z]/(g), with g the lexicographically first monic irreducible
polynomial of the prescribed degree. -/
abbrev CoefficientField (d : ℕ) (hd : 0 < d) := AdjoinRoot (firstPolynomial d hd)

instance firstPolynomial_fact (d : ℕ) (hd : 0 < d) : Fact (Irreducible (firstPolynomial d hd)) :=
  ⟨firstPolynomial_irreducible d hd⟩

instance coefficientField_finite (d : ℕ) (hd : 0 < d) : Finite (CoefficientField d hd) := by
  let : Module.Finite (ZMod 2) (CoefficientField d hd) :=
    (AdjoinRoot.powerBasis (firstPolynomial_monic d hd).ne_zero).finite
  exact Module.finite_of_finite (ZMod 2)

instance coefficientField_fintype (d : ℕ) (hd : 0 < d) : Fintype (CoefficientField d hd) :=
  Fintype.ofFinite _

@[instance_reducible] def coefficientFieldOrder (d : ℕ) (hd : 0 < d) :
    LinearOrder (CoefficientField d hd) :=
  letI : LinearOrder (Fin (firstPolynomial d hd).natDegree → ZMod 2) := vectorOrder
  LinearOrder.lift' (AdjoinRoot.powerBasisAux' (firstPolynomial_monic d hd)).equivFun
    (AdjoinRoot.powerBasisAux' (firstPolynomial_monic d hd)).equivFun.injective

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
namespace OAI

noncomputable section
open scoped Classical
open Polynomial Module
namespace KaplanskyCounterexample.Prescription
variable (K : Type) [Field K] [CharP K 2]

def rootSubfield (h : ℕ) : Subfield K :=
  RingHom.eqLocusField (iterateFrobenius K 2 h) (RingHom.id K)

@[simp] lemma mem_rootSubfield (h : ℕ) (x : K) : x ∈ rootSubfield K h ↔ x^(2^h)=x := Iff.rfl

variable [Fintype K]

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

abbrev Input := {h : ℕ // 2 ≤ h}

def fieldDegree (h : Input) : ℕ := h.val*(prime h.val-1)
lemma fieldDegree_pos (h : Input) : 0 < fieldDegree h := by
  have := prime_ge h.val h.property
  exact Nat.mul_pos (by omega) (by omega)

abbrev K (h : Input) := CoefficientField (fieldDegree h) (fieldDegree_pos h)
instance K_field (input : Input) : Field (K input) := inferInstance

instance K_char (h : Input) : CharP (K h) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (K h)).injective 2

instance K_order (h : Input) : LinearOrder (K h) := coefficientFieldOrder _ _

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped BigOperators
open Module
namespace KaplanskyCounterexample.FiniteGeometry

/-- Direct sum for distinct selections of at most m members of a family. -/
def ShortDirect {Q : Type u_12} {A : Type u_13} {ι : Type u_14} [Field Q] [AddCommGroup A] [Module Q A]
    (m : ℕ) (P : ι → Submodule Q A) : Prop :=
  ∀ (k : ℕ), k ≤ m → ∀ j : Fin k → ι, Function.Injective j →
    ∀ x : Fin k → A, (∀ i, x i ∈ P (j i)) → (∑ i, x i) = 0 → ∀ i, x i = 0

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {ι : Type u_3} [Field Q] [AddCommGroup A] [Module Q A]

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E]

structure DirectionFrame (Q : Type u_5) (A : Type u_6) (R : Type u_7) (E : Type u_8) [Field Q] [AddCommGroup A] [Module Q A]
    [AddCommGroup E] [Module Q E] where
  w : R → (Q × Q) →ₗ[Q] A
  e : (R × Q) → E →ₗ[Q] A
  winj : ∀ r, Function.Injective (w r)
  einj : ∀ j, Function.Injective (e j)
  direct : ShortDirect 10 (Sum.elim (fun r => (w r).range) (fun j => (e j).range))

namespace DirectionFrame
variable (F : DirectionFrame Q A R E)

def d (j : R × Q) : Q →ₗ[Q] A :=
  (F.w j.1).comp
    ({ toFun := fun t => (t, t * j.2)
       map_add' := by intro x y; simp only [add_mul, Prod.mk_add_mk]
       map_smul' := by intro x y; simp only [smul_eq_mul, mul_assoc, RingHom.id_apply, Prod.smul_mk] } : Q →ₗ[Q] Q × Q)

def exc (r : R) : Q →ₗ[Q] A := (F.w r).comp (LinearMap.inr Q Q Q)

def u (j : R × Q) : (Q × E) →ₗ[Q] A := (F.d j).coprod (F.e j)

def W (r : R) : Submodule Q A := (F.w r).range

def D (j : R × Q) : Submodule Q A := (F.d j).range

def U (j : R × Q) : Submodule Q A := (F.u j).range

def exceptional (r : R) : Submodule Q A := (F.exc r).range

@[simp] lemma d_apply (j : R × Q) (t : Q) : F.d j t = F.w j.1 (t, t * j.2) := rfl
@[simp] lemma exc_apply (r : R) (t : Q) : F.exc r t = F.w r (0,t) := rfl
@[simp] lemma u_apply (j : R × Q) (x : Q × E) : F.u j x = F.d j x.1 + F.e j x.2 := rfl

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
open Module
namespace KaplanskyCounterexample.FiniteGeometry

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI

noncomputable section
open Module
namespace KaplanskyCounterexample.FiniteGeometry

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Module
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A B R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup B] [Module Q B] [AddCommGroup E] [Module Q E]

namespace DirectionFrame

end DirectionFrame

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI

noncomputable section
namespace KaplanskyCounterexample.FiniteGeometry

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} [Field Q] [AddCommGroup A] [Module Q A] [Fintype A]

/-- Full finite affine cosets; no subset or segment convention is used. -/
def cosetPoints (U : Submodule Q A) (x : A) : Finset A :=
  Finset.univ.filter (fun y => y - x ∈ U)

@[simp] lemma mem_cosetPoints (U : Submodule Q A) (x y : A) :
    y ∈ cosetPoints U x ↔ y - x ∈ U := by simp only [cosetPoints, Finset.mem_filter, Finset.mem_univ, true_and]

lemma self_mem_cosetPoints (U : Submodule Q A) (x : A) : x ∈ cosetPoints U x := by simp only [mem_cosetPoints, sub_self, zero_mem]

lemma cosetPoints_eq {U : Submodule Q A} {x y : A} (h : y - x ∈ U) :
    cosetPoints U y = cosetPoints U x := by
  ext z
  simp only [mem_cosetPoints]
  constructor
  · intro hz
    convert U.add_mem hz h using 1; abel
  · intro hz
    convert U.sub_mem hz h using 1; abel

/-- A coset variable is its full point set, so no arbitrary representatives
enter the random choices. -/
def AffineCoset (U : Submodule Q A) := {C : Finset A // ∃ x, C = cosetPoints U x}

namespace AffineCoset
variable (U : Submodule Q A)

def of (x : A) : AffineCoset U := ⟨cosetPoints U x,x,rfl⟩

instance : Fintype (AffineCoset U) := by
  unfold AffineCoset
  infer_instance

lemma eq_of_mem {C : AffineCoset U} {x : A} (hx : x ∈ C.val) : of U x = C := by
  obtain ⟨y,hy⟩ := C.property
  apply Subtype.ext
  change cosetPoints U x = C.val
  rw [hy] at hx ⊢
  exact cosetPoints_eq ((mem_cosetPoints U y x).mp hx)

lemma mem_iff (C : AffineCoset U) (x : A) : x ∈ C.val ↔ of U x = C := by
  refine ⟨eq_of_mem U, ?_⟩
  intro hx
  rw [← hx]
  exact self_mem_cosetPoints U x

lemma of_eq_iff (x y : A) : of U x = of U y ↔ x - y ∈ U := by
  rw [← mem_iff]
  exact mem_cosetPoints U y x

end AffineCoset

variable [Fintype Q]

/-- A direction vector parametrizes every point of its full line. -/
def linePoints (x v : A) : Finset A := Finset.univ.image (fun t : Q => x + t • v)

/-- Affine lines are identified by their actual point sets. -/
def FullLine (s : Finset A) : Prop := ∃ x v : A, v ≠ 0 ∧ s = linePoints (Q := Q) x v

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
namespace KaplanskyCounterexample.FiniteGeometry

variable {α : Type u_1} {ι : Type u_2} [Fintype α]

/-- Independent selection of points at a prescribed probability. -/
def selectionMeasure (p : Set.Icc (0 : ℝ) 1) : Measure (α → Bool) :=
  Measure.pi fun _ => bernoulliMeasure true false p

instance (p : Set.Icc (0 : ℝ) 1) : IsProbabilityMeasure (selectionMeasure (α := α) p) := by
  unfold selectionMeasure
  infer_instance

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry

namespace HoleEvents
variable {Q : Type u_4} {A : Type u_5} {R : Type u_6} [Field Q] [AddCommGroup A] [Module Q A]
  [Fintype Q] [Fintype A] [Fintype R]
variable (S : Finset A) (W : R → Submodule Q A) (U : R × Q → Submodule Q A)

def PairIndex := Σ r : R, Σ x : S, {y : S // y ≠ x ∧ y.val - x.val ∈ W r}
instance : Fintype (PairIndex S W) := by unfold PairIndex; infer_instance

def OccupancyIndex (k : ℕ) := Σ j : R × Q, Σ r : R, Σ x : A,
  {f : Fin k → S // Function.Injective f ∧ ∀ i, (f i).val-x ∈ U j ⊔ W r}
instance (k : ℕ) : Fintype (OccupancyIndex S W U k) := by
  unfold OccupancyIndex; infer_instance

/-- Four cyclic corners, with side labels r,r',r,r'. -/
def corner (e : R → Q → A) (r r' : R) (x : A) (u v : Q) : Fin 4 → A :=
  ![x,x+e r u,x+e r u+e r' v,x+e r' v]

def sideLabel (r r' : R) : Fin 4 → R := ![r,r',r,r']

def RectangleIndex (e : R → Q → A) := Σ r : R, Σ r' : R, Σ x : A, Σ u : Q, Σ v : Q,
  {f : Fin 4 → S // Function.Injective f ∧ ∀ i,
      (f i).val - corner e r r' x u v i ∈ W (sideLabel r r' i)}
instance (e : R → Q → A) : Fintype (RectangleIndex S W e) := by
  unfold RectangleIndex; infer_instance

end HoleEvents
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry

namespace HoleEvents
variable {Q : Type u_5} {A : Type u_6} {R : Type u_7} [Field Q] [AddCommGroup A] [Module Q A]
  [Fintype Q] [Fintype A] [Fintype R]
variable (S : Finset A) (W : R → Submodule Q A) (U : R × Q → Submodule Q A)

end HoleEvents
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI

noncomputable section
namespace KaplanskyCounterexample.FiniteGeometry

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry

namespace DirectionFrame
variable {Q : Type u_2} {A : Type u_3} {R : Type u_4} {E : Type u_5} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype R] [Fintype E]

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E]

structure GenericStep (Q : Type u_5) (R : Type u_6) (E : Type u_7) [Zero E] where
  label : R × Q
  scalar : Q
  component : E
  nonzero : component ≠ 0

structure ExceptionalStep (Q : Type u_8) (R : Type u_9) [Zero Q] where
  label : R
  scalar : Q
  nonzero : scalar ≠ 0

abbrev PolygonStep (Q : Type u_10) (R : Type u_11) (E : Type u_12) [Zero Q] [Zero E] := GenericStep Q R E ⊕ ExceptionalStep Q R

namespace PolygonStep

def label : PolygonStep Q R E → (R × Q) ⊕ R
  | .inl g => .inl g.label
  | .inr e => .inr e.label

def vector (F : DirectionFrame Q A R E) : PolygonStep Q R E → A
  | .inl g => F.u g.label (g.scalar,g.component)
  | .inr e => F.exc e.label e.scalar

end PolygonStep

namespace DirectionFrame
variable (F : DirectionFrame Q A R E)

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E]

namespace DirectionFrame
variable (F : DirectionFrame Q A R E)

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {I : Type u_1} {J : Type u_2} {R : Type u_3} [Fintype I] [DecidableEq J] [DecidableEq R]

def genericLabels (lab : I → J ⊕ R) : Finset J := (Finset.univ.image lab).toLeft

@[simp] lemma mem_genericLabels (lab : I → J ⊕ R) (j : J) :
    j ∈ genericLabels lab ↔ ∃ i, lab i = .inl j := by simp only [genericLabels, Finset.mem_toLeft, Finset.mem_image, Finset.mem_univ, true_and]

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E]

namespace DirectionFrame
variable (F : DirectionFrame Q A R E)

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E]

instance [Fintype Q] [Fintype R] [Fintype E] : Fintype (GenericStep Q R E) :=
  Fintype.ofInjective (fun g => (g.label,g.scalar,g.component)) (by
    rintro ⟨l,t,x,hx⟩ ⟨l',t',x',hx'⟩ h
    cases Prod.mk.inj h with
    | intro hl hrest =>
      cases hl
      obtain ⟨ht,hx⟩ := Prod.mk.inj hrest
      cases ht; cases hx; rfl)
instance [Fintype Q] [Fintype R] : Fintype (ExceptionalStep Q R) :=
  Fintype.ofInjective (fun g => (g.label,g.scalar)) (by
    rintro ⟨l,t,ht⟩ ⟨l',t',ht'⟩ h
    obtain ⟨hl,he⟩ := Prod.mk.inj h
    cases hl; cases he; rfl)

namespace PolygonStep
end PolygonStep

structure Candidate (F : DirectionFrame Q A R E) (T : R → Finset A) (k : ℕ) where
  step : Fin k → PolygonStep Q R E
  point : Fin k → A
  shift : ∀ i, point (finRotate k i) - point i = (step i).vector F
  adjacent : ∀ i, (step i).label ≠ (step (finRotate k i)).label
  exceptional : ∀ i (e : ExceptionalStep Q R), step i = .inr e →
    point i ∈ T e.label ∧ point (finRotate k i) ∈ T e.label
  generic : ∃ i j, (step i).label = .inl j

namespace Candidate
variable (F : DirectionFrame Q A R E) (T : R → Finset A) {k : ℕ}

@[ext] lemma ext {c d : Candidate F T k} (hs : c.step = d.step) (hp : c.point = d.point) : c=d := by
  cases c; cases d; cases hs; cases hp; rfl

instance [Fintype Q] [Fintype R] [Fintype E] [Fintype A] : Fintype (Candidate F T k) :=
  Fintype.ofInjective (fun c => (c.step,c.point)) (by
    intro c d h
    exact ext F T (congrArg Prod.fst h) (congrArg Prod.snd h))

end Candidate

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A]

namespace Candidate
variable (F : DirectionFrame Q A R E) (T : R → Finset A) (k : ℕ)
variable (j : R × Q) (C : AffineCoset (F.U j))

structure Rooted where
  cycle : Candidate F T k
  root : Fin k
  label_eq : (cycle.step root).label = .inl j
  point_mem : cycle.point root ∈ C.val

namespace Rooted
@[ext] lemma ext {c d : Rooted F T k j C} (hc : c.cycle = d.cycle) (hr : c.root = d.root) : c=d := by
  cases c; cases d; cases hc; cases hr; rfl
instance [Fintype Q] [Fintype R] [Fintype E] : Fintype (Rooted F T k j C) :=
  Fintype.ofInjective (fun c => (c.cycle,c.root)) (by
    intro c d h
    exact ext F T k j C (congrArg Prod.fst h) (congrArg Prod.snd h))
end Rooted

/-- A deliberately generous finite codec. The last field stores k exceptional
scalars rather than just one; the final numeric load still tends to zero. -/
structure TwoCode where
  other : R × Q
  idx : Fin 4 → Fin k
  tag : Fin k → Fin 3
  point : C.val
  vec0 : Q × E
  vec1 : Q × E
  exc : Fin k → Q

instance [Fintype Q] [Fintype R] [Fintype E] : Fintype (TwoCode F k j C) :=
  Fintype.ofInjective (fun c => (c.other,c.idx,c.tag,c.point,c.vec0,c.vec1,c.exc)) (by
    rintro ⟨a,b,c,d,e,f,g⟩ ⟨a',b',c',d',e',f',g'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := h
    rfl)

end Candidate
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype Q] [Fintype A]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)

def replacementRegion (r : R) : Finset A := O.biUnion (fun o => cosetPoints (F.W r) o)

omit [Fintype Q] in
@[simp] lemma mem_replacementRegion (r : R) (x : A) :
    x ∈ F.replacementRegion O r ↔ ∃ o ∈ O, x-o ∈ F.W r := by
  simp only [replacementRegion, Finset.mem_biUnion, mem_cosetPoints]

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A]

namespace Candidate
variable (F : DirectionFrame Q A R E) (T : R → Finset A) (k : ℕ)
variable (j : R × Q) (C : AffineCoset (F.U j))

local instance oneCodeIndexNeZero : NeZero (2 : ℕ) := inferInstance

namespace OneCode
end OneCode

end Candidate
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A]

abbrev SlabVariable (F : DirectionFrame Q A R E) := Σ j : R × Q, AffineCoset (F.U j)

namespace Candidate
variable (F : DirectionFrame Q A R E) (T : R → Finset A) {k : ℕ} (c : Candidate F T k)

abbrev Occurrence := {p : Fin k × GenericStep Q R E // c.step p.1 = .inl p.2}

omit [Fintype A] in
lemma occurrence_index_injective : Function.Injective (fun p : c.Occurrence F T => p.val.1) := by
  intro p p' h
  apply Subtype.ext
  apply Prod.ext h
  have hs : c.step p.val.1 = c.step p'.val.1 := congrArg c.step h
  exact Sum.inl.inj (p.property.symm.trans (hs.trans p'.property))

instance : Fintype (c.Occurrence F T) :=
  Fintype.ofInjective (fun p => p.val.1) (c.occurrence_index_injective F T)

def occurrenceVariable (p : c.Occurrence F T) : SlabVariable F :=
  ⟨p.val.2.label,AffineCoset.of (F.U p.val.2.label) (c.point p.val.1)⟩

def occurrenceVector (p : c.Occurrence F T) : E := p.val.2.component

def deps : Finset (SlabVariable F) := Finset.univ.image (c.occurrenceVariable F T)

def constraintVector (v : SlabVariable F) : E :=
  if h : ∃ p : c.Occurrence F T, c.occurrenceVariable F T p = v
    then c.occurrenceVector F T h.choose else 0

end Candidate
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype R] [Fintype E]
namespace Candidate
variable (F : DirectionFrame Q A R E) (T : R → Finset A) (k : ℕ)
variable (j : R × Q) (C : AffineCoset (F.U j))

end Candidate
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace KaplanskyCounterexample.FiniteLocalLemma

variable {Ω : Type u_1} {ι : Type u_2}

/-- Avoid a finite list of bad events. -/
def avoid (E : ι → Set Ω) (s : Finset ι) : Set Ω := ⋂ i ∈ s, (E i)ᶜ

@[simp] lemma mem_avoid {E : ι → Set Ω} {s : Finset ι} {ω : Ω} :
    ω ∈ avoid E s ↔ ∀ i ∈ s, ω ∉ E i := by simp only [avoid, mem_iInter, mem_compl_iff]

@[simp] lemma avoid_empty (E : ι → Set Ω) : avoid E ∅ = Set.univ := by
  simp only [avoid, Finset.notMem_empty, iInter_of_empty, iInter_univ]

variable [DecidableEq ι]

variable [MeasurableSpace Ω]

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {E : ι → Set Ω}

section Weighted
variable {κ : Type u_3} [DecidableEq κ] [Fintype ι]

end Weighted

section IndependentVariables
variable {κ : Type u_4} {β : Type u_5} [DecidableEq κ]

variable [MeasurableSpace β] [MeasurableSingletonClass β] [Finite β]

end IndependentVariables

end KaplanskyCounterexample.FiniteLocalLemma

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
open Module MeasureTheory

variable {Q : Type u_6} {E : Type u_7} [Field Q] [AddCommGroup E] [Module Q E]

abbrev Plane (Q : Type u_8) (E : Type u_9) [Field Q] [AddCommGroup E] [Module Q E] :=
  {P : Submodule Q E // finrank Q P = 2}

instance [Finite E] : Finite (Plane Q E) := by
  unfold Plane
  infer_instance

instance [Fintype E] : Fintype (Plane Q E) := Fintype.ofFinite _

local instance identityRingHomSurjective : RingHomSurjective (RingHom.id Q) := inferInstance

/-- An ambient automorphism permutes the plane sample space. -/
def mapPlane (g : E ≃ₗ[Q] E) : Plane Q E ≃ Plane Q E where
  toFun P := ⟨P.val.map g.toLinearMap, by rw [g.finrank_map_eq]; exact P.property⟩
  invFun P := ⟨P.val.map g.symm.toLinearMap, by rw [g.symm.finrank_map_eq]; exact P.property⟩
  left_inv P := by
    apply Subtype.ext
    ext x
    simp only [Submodule.mem_map_equiv, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]
  right_inv P := by
    apply Subtype.ext
    ext x
    simp only [Submodule.mem_map_equiv, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]

@[simp] theorem mem_mapPlane (g : E ≃ₗ[Q] E) (P : Plane Q E) (x : E) :
    g x ∈ (mapPlane g P).val ↔ x ∈ P.val := by
  change g x ∈ P.val.map g.toLinearMap ↔ x ∈ P.val
  simp only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

variable [Fintype Q] [Fintype E]

end KaplanskyCounterexample.FiniteGeometry

namespace KaplanskyCounterexample.FiniteGeometry
open Module MeasureTheory ProbabilityTheory
open KaplanskyCounterexample.FiniteLocalLemma

variable {Q : Type u_12} {E : Type u_13} {κ : Type u_14} {ι : Type u_15} [Field Q] [AddCommGroup E] [Module Q E]
  [Fintype Q] [Fintype E] [Fintype κ] [Nonempty (Plane Q E)]
  [MeasurableSpace (Plane Q E)] [MeasurableSingletonClass (Plane Q E)]

/-- Independent choices of uniformly distributed slab direction planes. -/
def slabMeasure : Measure (κ → Plane Q E) :=
  Measure.pi fun _ => (PMF.uniformOfFintype (Plane Q E)).toMeasure

instance : IsProbabilityMeasure (slabMeasure (Q := Q) (E := E) (κ := κ)) := by
  unfold slabMeasure
  infer_instance

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
open KaplanskyCounterexample.FiniteLocalLemma
namespace KaplanskyCounterexample.FiniteGeometry

variable {Q : Type u_2} {A : Type u_3} {R : Type u_4} {E : Type u_5} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype R] [Fintype E]
namespace Candidate
variable (F : DirectionFrame Q A R E) (T : R → Finset A) (k : ℕ)

end Candidate
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)

lemma diff_mem_coset {j : R × Q} (C : AffineCoset (F.U j)) {x y : A}
    (hx : x ∈ C.val) (hy : y ∈ C.val) : y-x ∈ F.U j := by
  have he := (AffineCoset.eq_of_mem _ hy).trans (AffineCoset.eq_of_mem _ hx).symm
  exact (AffineCoset.of_eq_iff _ _ _).mp he

abbrev LocalHolePair (v : SlabVariable F) :=
  {xy : ↥(O ∩ v.2.val) × ↥(O ∩ v.2.val) // xy.1 ≠ xy.2}

def localHolePairVector (v : SlabVariable F) (p : F.LocalHolePair O v) : Q × E :=
  (F.diff_mem_coset v.2 (Finset.mem_inter.mp p.val.1.property).2
    (Finset.mem_inter.mp p.val.2.property).2).choose

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
open KaplanskyCounterexample.FiniteLocalLemma
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype R] [Fintype E]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)

abbrev ShortCandidate := Σ i : Fin 3, Candidate F (F.replacementRegion O) (i.val+3)
abbrev SlabEvent := (Σ v : SlabVariable F, F.LocalHolePair O v) ⊕ F.ShortCandidate O

instance : Fintype (F.ShortCandidate O) := by unfold ShortCandidate; infer_instance
instance : Fintype (F.SlabEvent O) := by unfold SlabEvent; infer_instance

structure SuccessfulSlabs (P : SlabVariable F → Plane Q E) : Prop where
  holes : ∀ v (p : F.LocalHolePair O v), (F.localHolePairVector O v p).2 ∉ (P v).val
  candidates : ∀ k, 3 ≤ k → k ≤ 5 → ∀ c : Candidate F (F.replacementRegion O) k,
    ∃ v ∈ c.deps F (F.replacementRegion O), c.constraintVector F (F.replacementRegion O) v ∉ (P v).val

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI

noncomputable section
namespace KaplanskyCounterexample.FiniteGeometry

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
namespace DirectionFrame
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype R] [Fintype E]

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} [Field Q] [AddCommGroup A] [Module Q A] [Fintype Q] [Fintype A]

omit [Fintype A] in
@[simp] lemma mem_linePoints (x v y : A) :
    y ∈ linePoints (Q := Q) x v ↔ ∃ t : Q, x + t • v = y := by
  simp only [linePoints, Finset.mem_image, Finset.mem_univ, true_and]

/-- A partition by full lines, represented without arbitrary labels or duplicates. -/
structure LinePartition where
  through : A → Finset A
  self : ∀ x, x ∈ through x
  full : ∀ x, FullLine (Q := Q) (through x)
  stable : ∀ x y, y ∈ through x → through y = through x

namespace LinePartition
variable (L : LinePartition (Q := Q) (A := A))
end LinePartition
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {B : Type u_3} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup B] [Module Q B] [Fintype Q] [Fintype A] [Fintype B]

namespace PartitionOn
variable (f : B →ₗ[Q] A) (hf : Function.Injective f) (o : A)

local instance identityRingHomSurjective : RingHomSurjective (RingHom.id Q) := inferInstance

def parametrization : B ≃ ↥(cosetPoints f.range o) :=
  Equiv.ofBijective (fun x => ⟨o+f x,by simp only [mem_cosetPoints, add_sub_cancel_left, LinearMap.mem_range, exists_apply_eq_apply]⟩) (by
    constructor
    · intro x y h; exact hf (add_left_cancel (congrArg Subtype.val h))
    · rintro ⟨y,hy⟩
      obtain ⟨x,hx⟩ := (mem_cosetPoints _ _ _).mp hy
      exact ⟨x,Subtype.ext (by change o+f x=y; rw [hx]; abel)⟩)

omit [Fintype Q] [Fintype B] in
@[simp] lemma parametrization_val (x : B) : (parametrization f hf o x).val = o+f x := rfl

omit [Fintype Q] [Fintype B] in
@[simp] lemma parametrization_symm_apply (x : ↥(cosetPoints f.range o)) :
    o+f ((parametrization f hf o).symm x)=x.val := by
  exact congrArg Subtype.val ((parametrization f hf o).apply_symm_apply x)

end PartitionOn

section Glue
variable {ι : Type u_4} (S : ι → Finset A) (key : A → ι) (hmem : ∀ x, x ∈ S (key x)) (hkey : ∀ x y, y ∈ S (key x) → key y=key x)

end Glue
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E)

local instance identityRingHomSurjective : RingHomSurjective (RingHom.id Q) := inferInstance

def slabMap (j : R × Q) (P : Plane Q E) : (P.val × Q) →ₗ[Q] A where
  toFun x := F.u j (x.2,x.1.val)
  map_add' x y := by simpa only [Prod.snd_add, Prod.fst_add, Submodule.coe_add, u_apply, d_apply, map_add, Prod.mk_add_mk] using (F.u j).map_add (x.2,x.1.val) (y.2,y.1.val)
  map_smul' c x := by simpa only [Prod.smul_snd, smul_eq_mul, Prod.smul_fst, SetLike.val_smul, u_apply, d_apply, map_smul, RingHom.id_apply, smul_add, add_left_inj, Prod.smul_mk] using (F.u j).map_smul c (x.2,x.1.val)

omit [Fintype A] in
@[simp] lemma slabMap_axis (j : R × Q) (P : Plane Q E) (t : Q) :
    F.slabMap j P (0,t) = F.d j t := by simp only [slabMap, u_apply, d_apply, LinearMap.coe_mk, AddHom.coe_mk, ZeroMemClass.coe_zero, map_zero, add_zero]

variable (P : SlabVariable F → Plane Q E) (j : R × Q)

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical
open Module
namespace KaplanskyCounterexample.FiniteGeometry

variable {Q : Type u_1} {P : Type u_2} [Field Q] [AddCommGroup P] [Module Q P]

def slabLine (J : P →ₗ[Q] P) (γ : P →ₗ[Q] Q) : Set (P × Q) :=
  {p | γ p.1 = 1 ∧ p.2 = γ (J p.1)}

variable {F : Type u_3} [Field F] [Algebra Q F]

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical
open Module
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {P : Type u_2} [Field Q] [AddCommGroup P] [Module Q P] [Fintype Q] [Fintype P]

def slabLinePoints (J : P →ₗ[Q] P) (γ : P →ₗ[Q] Q) : Finset (P × Q) :=
  Finset.univ.filter (fun p => p ∈ slabLine J γ)

@[simp] lemma mem_slabLinePoints (J : P →ₗ[Q] P) (γ : P →ₗ[Q] Q) (p : P × Q) :
    p ∈ slabLinePoints J γ ↔ p ∈ slabLine J γ := by simp only [slabLinePoints, Finset.mem_filter, Finset.mem_univ, true_and]

def modelAxis : Finset (P × Q) := linePoints (Q := Q) 0 (0,1)

omit [Fintype P] in
@[simp] lemma mem_modelAxis (p : P × Q) : p ∈ modelAxis (Q := Q) (P := P) ↔ p.1=0 := by
  change p ∈ linePoints (Q := Q) 0 (0,1) ↔ p.1=0
  constructor
  · intro membership
    obtain ⟨scalar,rfl⟩ := (mem_linePoints _ _ _).mp membership
    exact (zero_add (scalar • (0 : P))).trans (smul_zero scalar)
  · intro first_zero
    apply (mem_linePoints _ _ _).mpr
    refine ⟨p.2,Prod.ext ?_ ?_⟩
    · exact ((zero_add _).trans (smul_zero p.2)).trans first_zero.symm
    · exact (zero_add _).trans (mul_one p.2)

variable [FiniteDimensional Q P] (hd : finrank Q P = 2) (J : P →ₗ[Q] P)

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical
open Module
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype E]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (j : R × Q) (P : Plane Q E)

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI

noncomputable section
open Module
namespace KaplanskyCounterexample.FiniteGeometry

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A R E : Type} [Field Q] [CharP Q 2] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype E]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (O : Finset A)
  (P : SlabVariable F → Plane Q E) (hP : F.SuccessfulSlabs O P)

structure Preliminary where
  part : R × Q → LinePartition (Q := Q) (A := A)
  axis : ∀ j o, o ∈ O → (part j).through o = cosetPoints (F.D j) o
  generic : ∀ j x, Disjoint ((part j).through x) O →
    ∀ y ∈ (part j).through x, ∀ z ∈ (part j).through x, z ≠ y →
    ∃ c : Q, ∃ e : E, e ≠ 0 ∧ e ∈ (P ⟨j,AffineCoset.of (F.U j) y⟩).val ∧ F.u j (c,e)=z-y

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E)

def replacementLine (r : R) (o : A) (a : Q) : Finset A :=
  cosetPoints (F.exceptional r) (o+F.w r (a,0))

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)
  (P : SlabVariable F → Plane Q E) (T : F.Preliminary O P)

def LiveLine (j : R × Q) := {l : Finset A // (∃ x, (T.part j).through x=l) ∧ Disjoint l O}
def LiveIndex := Σ j, F.LiveLine O P T j
def NewIndex := R × O × {a : Q // a ≠ 0}
def TradeIndex := F.LiveIndex O P T ⊕ NewIndex (Q := Q) (R := R) O

instance [Fintype R] : Fintype (F.LiveIndex O P T) := by unfold LiveIndex LiveLine; infer_instance
instance [Fintype R] : Fintype (F.TradeIndex O P T) := by unfold TradeIndex NewIndex; infer_instance

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype R]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)
  (P : SlabVariable F → Plane Q E) (T : F.Preliminary O P)

def KeptAt (x : A) := {j : R × Q // Disjoint ((T.part j).through x) O}
def RemovedAt (x : A) := {j : R × Q // ¬ Disjoint ((T.part j).through x) O}
def NewAt (x : A) := {i : NewIndex (Q := Q) (R := R) O //
  x ∈ F.replacementLine i.1 i.2.1.val i.2.2.val}
def LiveAt (x : A) := {i : F.LiveIndex O P T // x ∈ i.2.val}

instance (x : A) : Fintype (F.NewAt O x) := by unfold NewAt NewIndex; infer_instance
instance (x : A) : Fintype (F.LiveAt O P T x) := by unfold LiveAt; infer_instance
instance (x : A) : Fintype (F.KeptAt O P T x) := by unfold KeptAt; infer_instance
instance (x : A) : Fintype (F.RemovedAt O P T x) := by unfold RemovedAt; infer_instance

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (O : Finset A)
  (P : SlabVariable F → Plane Q E) (T : F.Preliminary O P)

end DirectionFrame

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
namespace OAI


noncomputable section
open scoped Classical
namespace SimpleGraph
open scoped _root_.SimpleGraph
open _root_.SimpleGraph _root_.OAI.SimpleGraph Walk
variable {V : Type u_1} {G : _root_.SimpleGraph V}

/-- A walk has no immediate backtracking when it has no closed subwalk
of length two. This formulation is hereditary under taking subwalks. -/
def Walk.Reduced {u v : V} (p : G.Walk u v) : Prop :=
  ∀ (w : V) (q : G.Walk w w), q.IsSubwalk p → q.length ≠ 2

lemma Walk.Reduced.of_isSubwalk {u v w x : V} {p : G.Walk u v} {q : G.Walk w x}
    (hp : _root_.OAI.SimpleGraph.Walk.Reduced p) (hq : q.IsSubwalk p) : _root_.OAI.SimpleGraph.Walk.Reduced q := by
  intro z r hr
  exact hp z r (hr.trans hq)

lemma Walk.Reduced.copy {u v u' v' : V} {p : G.Walk u v}
    (hp : _root_.OAI.SimpleGraph.Walk.Reduced p) (hu : u = u') (hv : v = v') : _root_.OAI.SimpleGraph.Walk.Reduced (p.copy hu hv) := by
  subst u' v'
  exact hp

/-- A nonempty closed walk with no immediate backtracking contains a cycle
no longer than itself. This is the girth fact used for facial boundaries. -/
theorem Walk.Reduced.exists_cycle {u : V} {p : G.Walk u u}
    (hp : _root_.OAI.SimpleGraph.Walk.Reduced p) (hne : ¬ p.Nil) :
    ∃ (v : V) (q : G.Walk v v), q.IsCycle ∧ q.length ≤ p.length := by
  classical
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing u p with
  | h n ih =>
    by_cases ht : p.tail.IsPath
    · have hlen : 3 ≤ p.length := by
        have hpos : 0 < p.length := Nat.pos_of_ne_zero (fun h => hne (length_eq_zero_iff.mp h))
        have hnotone : p.length ≠ 1 := by
          intro h
          exact G.irrefl (p.adj_of_length_eq_one h)
        have hnottwo := hp u p p.isSubwalk_rfl
        omega
      exact ⟨u, p, (isCycle_iff_isPath_tail_and_le_length).mpr ⟨ht, hlen⟩, by omega⟩
    · rw [isPath_iff_isSubwalk_imp_nil] at ht
      push Not at ht
      obtain ⟨v, q, hsub, hq⟩ := ht
      have hqt : q.IsSubwalk p := hsub.trans p.isSubwalk_rfl.tail
      have hqred : _root_.OAI.SimpleGraph.Walk.Reduced q := hp.of_isSubwalk hqt
      have hlt : q.length < n := by
        have := length_le_of_isSubwalk hsub
        have htlen := p.length_tail
        have hpos : 0 < p.length := Nat.pos_of_ne_zero (fun h => hne (length_eq_zero_iff.mp h))
        omega
      obtain ⟨w, r, hr, hlen⟩ := ih q.length hlt hqred hq rfl
      exact ⟨w, r, hr, hlen.trans (by simpa only [hn] using length_le_of_isSubwalk hqt)⟩

lemma Walk.Reduced.egirth_le {u : V} {p : G.Walk u u}
    (hp : _root_.OAI.SimpleGraph.Walk.Reduced p) (hne : ¬ p.Nil) : G.egirth ≤ p.length := by
  obtain ⟨v, q, hq, hlen⟩ := hp.exists_cycle hne
  exact hq.egirth_le_length.trans (by exact_mod_cast hlen)

/-- The elementary vertex-index criterion for no immediate backtracking. -/
lemma Walk.reduced_of_getVert {u v : V} (p : G.Walk u v)
    (h : ∀ i, i + 2 ≤ p.length → p.getVert i ≠ p.getVert (i + 2)) : _root_.OAI.SimpleGraph.Walk.Reduced p := by
  intro w q hq hlen
  obtain ⟨r, s, rfl⟩ := hq
  have hi : r.length + 2 ≤ ((r.append q).append s).length := by
    simp only [length_append, hlen]
    omega
  have hstart : ((r.append q).append s).getVert r.length = w := by
    rw [getVert_append', if_pos (by simp only [length_append]; omega),
      getVert_append', if_pos le_rfl, getVert_length]
  have hend : ((r.append q).append s).getVert (r.length + 2) = w := by
    rw [getVert_append', if_pos (by simp only [length_append, hlen, Std.le_refl]),
      getVert_append, if_neg (by omega)]
    simpa only [add_tsub_cancel_left, hlen] using q.getVert_length
  exact h r.length hi (hstart.trans hend.symm)

end SimpleGraph

end

end OAI
end

section
namespace OAI



section

noncomputable section
open scoped Classical

noncomputable section
open scoped Classical BigOperators
open Equiv Equiv.Perm
namespace OddKaplansky.Planar
attribute [local simp] SameCycle.rfl

variable {α : Type portUniverse1} [Fintype α]

abbrev Cycles (p : Perm α) := Quotient (SameCycle.setoid p)

def cycleClass (p : Perm α) (x : α) : Cycles p := Quotient.mk _ x

def cycleSet (p : Perm α) (c : Cycles p) : Finset α :=
  Finset.univ.filter fun x => cycleClass p x = c

lemma mem_cycleSet (p : Perm α) (c : Cycles p) (x : α) :
    x ∈ cycleSet p c ↔ cycleClass p x = c := by simp only [cycleSet, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype α] in
lemma cycleClass_eq (p : Perm α) (x y : α) :
    cycleClass p x = cycleClass p y ↔ p.SameCycle x y := Quotient.eq

lemma cycleSet_nonempty (p : Perm α) (c : Cycles p) : (cycleSet p c).Nonempty := by
  induction c using Quotient.inductionOn with
  | h x => exact ⟨x, (mem_cycleSet p _ x).mpr rfl⟩

lemma cycles_sum_card (p : Perm α) :
    ∑ c : Cycles p, (cycleSet p c).card = Fintype.card α := by
  classical
  simpa only [cycleSet, Finset.mem_univ, Finset.filter_true, Finset.card_univ] using Finset.sum_card_fiberwise_eq_card_filter
    (s := Finset.univ) (t := Finset.univ) (g := cycleClass p)

structure Ribbon (α : Type portUniverse2) where
  black : Perm α
  white : Perm α

def Ribbon.face (R : Ribbon α) : Perm α := R.white * R.black

def Ribbon.mergeWhite (R : Ribbon α) (e : α) : Ribbon α where
  black := R.black
  white := swap e (R.face e) * R.white

omit [Fintype α] in
lemma mergeWhite_face (R : Ribbon α) (e : α) :
    (R.mergeWhite e).face = swap e (R.face e) * R.face := by
  simp only [Ribbon.face, Ribbon.mergeWhite, coe_mul, Function.comp_apply, mul_assoc]

lemma sameCycle_map {β : Type portUniverse3} (p : Perm α) (q : Perm β) (f : α → β)
    (hstep : ∀ x, q.SameCycle (f x) (f (p x))) {x y : α}
    (hxy : p.SameCycle x y) : q.SameCycle (f x) (f y) := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => simp only [pow_zero, coe_one, id_eq, SameCycle.rfl]
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (hstep _)

def unplug (p : Perm α) (a : α) : Perm α := swap a (p a) * p

def bypass (p : Perm α) (a x : α) : α := if x = a then p a else x

omit [Fintype α] in
lemma unplug_fixed (p : Perm α) (a : α) : unplug p a a = a := by
  simp only [unplug, coe_mul, Function.comp_apply, swap_apply_right]

lemma unplug_sameCycle (p : Perm α) (a : α) {x y : α}
    (h : (unplug p a).SameCycle x y) : p.SameCycle x y := by
  apply sameCycle_map (unplug p a) p id _ h
  intro x
  change p.SameCycle x (swap a (p a) (p x))
  by_cases hx : x = a
  · subst x
    simp only [swap_apply_right, SameCycle.rfl]
  · by_cases hxa : p x = a
    · simp only [hxa, swap_apply_left]
      exact (show p.SameCycle x a by rw [← hxa]; simp only [sameCycle_apply_right, SameCycle.rfl]).trans (by simp only [sameCycle_apply_right, SameCycle.rfl])
    · have hxp : p x ≠ p a := p.injective.ne hx
      rw [swap_apply_of_ne_of_ne hxa hxp]
      simp only [sameCycle_apply_right, SameCycle.rfl]

lemma sameCycle_bypass (p : Perm α) (a : α) (ha : p a ≠ a) {x y : α}
    (h : p.SameCycle x y) :
    (unplug p a).SameCycle (bypass p a x) (bypass p a y) := by
  apply sameCycle_map p (unplug p a) (bypass p a) _ h
  intro x
  by_cases hx : x = a
  · subst x
    simp only [bypass, ↓reduceIte, ha, SameCycle.rfl]
  · by_cases hxa : p x = a
    · have hq : unplug p a x = p a := by simp only [unplug, coe_mul, Function.comp_apply, hxa, swap_apply_left]
      simp only [bypass, hx, hxa, ite_false, ite_true]
      rw [← hq]
      simp only [sameCycle_apply_right, SameCycle.rfl]
    · have hxp : p x ≠ p a := p.injective.ne hx
      have hq : unplug p a x = p x := by
        simp only [unplug, Perm.mul_apply]
        exact swap_apply_of_ne_of_ne hxa hxp
      simp only [bypass, hx, hxa, ite_false]
      rw [← hq]
      simp only [sameCycle_apply_right, SameCycle.rfl]

lemma unplug_sameCycle_iff (p : Perm α) (a : α) (ha : p a ≠ a)
    {x y : α} (hx : x ≠ a) (hy : y ≠ a) :
    (unplug p a).SameCycle x y ↔ p.SameCycle x y := by
  refine ⟨unplug_sameCycle p a, fun h => ?_⟩
  simpa only [bypass, hx, ↓reduceIte, hy] using sameCycle_bypass p a ha h

omit [Fintype α] in
lemma bypass_ne (p : Perm α) (a : α) (ha : p a ≠ a) (x : α) :
    bypass p a x ≠ a := by
  by_cases hx : x = a <;> simp only [bypass, hx, ↓reduceIte, ne_eq, ha, not_false_eq_true]

def unplugCycleEquiv (p : Perm α) (a : α) (ha : p a ≠ a) :
    Cycles p ≃ {c : Cycles (unplug p a) // c ≠ cycleClass (unplug p a) a} where
  toFun := Quotient.lift (fun x =>
    ⟨cycleClass (unplug p a) (bypass p a x), by
      intro h
      have he := (cycleClass_eq _ _ _).mp h
      exact bypass_ne p a ha x (he.eq_of_right (unplug_fixed p a))⟩)
    (fun x y h => Subtype.ext ((cycleClass_eq _ _ _).mpr (sameCycle_bypass p a ha h)))
  invFun c := Quotient.map' id (fun _ _ h => unplug_sameCycle p a h) c.val
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h x =>
      change cycleClass p (bypass p a x) = cycleClass p x
      apply (cycleClass_eq _ _ _).mpr
      by_cases hx : x = a <;> simp only [bypass, hx, ↓reduceIte, sameCycle_apply_left, SameCycle.rfl]
  right_inv c := by
    rcases c with ⟨c, hc⟩
    apply Subtype.ext
    induction c using Quotient.inductionOn with
    | h x =>
      have hx : x ≠ a := by
        intro h
        apply hc
        exact congrArg (cycleClass _) h
      change cycleClass (unplug p a) (bypass p a x) = cycleClass (unplug p a) x
      simp only [bypass, hx, ↓reduceIte]

lemma unplug_cycles_card (p : Perm α) (a : α) (ha : p a ≠ a) :
    Nat.card (Cycles (unplug p a)) = Nat.card (Cycles p) + 1 := by
  have h := Fintype.card_congr (unplugCycleEquiv p a ha)
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h
  have hp : 0 < Fintype.card (Cycles (unplug p a)) :=
    Fintype.card_pos_iff.mpr ⟨cycleClass (unplug p a) a⟩
  simp only [Nat.card_eq_fintype_card]
  omega

lemma swap_mul_sameCycle (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b) :
    (swap a b * p).SameCycle a b := by
  have hret : ∃ n : ℕ, 0 < n ∧ (p ^ n) b = b := by
    exact ⟨orderOf p, orderOf_pos p, by simp only [pow_orderOf_eq_one, coe_one, id_eq]⟩
  let n := Nat.find hret
  have hn : 0 < n ∧ (p ^ n) b = b := Nat.find_spec hret
  have hmin : ∀ k, 0 < k → k < n → (p ^ k) b ≠ b := by
    intro k hk hkn heq
    exact Nat.find_min hret hkn ⟨hk, heq⟩
  have hneq : ∀ k : ℕ, (p ^ k) b ≠ a := by
    intro k heq
    apply hab
    exact (show p.SameCycle b a from ⟨k, by simpa only [zpow_natCast] using heq⟩).symm
  have hiter : ∀ k, k < n → ((swap a b * p) ^ k) b = (p ^ k) b := by
    intro k
    induction k with
    | zero => simp only [pow_zero, coe_one, id_eq, implies_true]
    | succ k ih =>
      intro hk
      rw [pow_succ', Perm.mul_apply, ih (by omega), Perm.mul_apply]
      have heq : p ((p ^ k) b) = (p ^ (k + 1)) b := by
        rw [pow_succ', Perm.mul_apply]
      rw [heq, swap_apply_of_ne_of_ne (hneq _) (hmin _ (by omega) hk)]
  have hn' : n - 1 + 1 = n := by omega
  have hstep : ((swap a b * p) ^ n) b = a := by
    rw [← hn', pow_succ', Perm.mul_apply, hiter _ (by omega), Perm.mul_apply]
    have heq : p ((p ^ (n - 1)) b) = b := by
      calc
        p ((p ^ (n - 1)) b) = (p ^ (n - 1 + 1)) b := by rw [pow_succ', Perm.mul_apply]
        _ = b := by rw [hn']; exact hn.2
    rw [heq, swap_apply_right]
  exact (show (swap a b * p).SameCycle b a from ⟨n, by simpa only [zpow_natCast] using hstep⟩).symm

lemma sameCycle_swap_mul (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b)
    {x y : α} (hxy : p.SameCycle x y) : (swap a b * p).SameCycle x y := by
  have hlink := swap_mul_sameCycle p a b hab
  apply sameCycle_map p (swap a b * p) id _ hxy
  intro x
  have hx : (swap a b * p).SameCycle x (swap a b (p x)) := by
    change (swap a b * p).SameCycle x ((swap a b * p) x)
    exact SameCycle.apply_right SameCycle.rfl
  by_cases hxa : p x = a
  · rw [hxa, swap_apply_left] at hx
    exact hx.trans (hxa ▸ hlink.symm)
  · by_cases hxb : p x = b
    · rw [hxb, swap_apply_right] at hx
      exact hx.trans (hxb ▸ hlink)
    · rwa [swap_apply_of_ne_of_ne hxa hxb] at hx

def mergedClass (p : Perm α) (a b : α) (x : α) : Cycles p :=
  if cycleClass p x = cycleClass p b then cycleClass p a else cycleClass p x

omit [Fintype α] in
lemma cycleClass_apply (p : Perm α) (x : α) : cycleClass p (p x) = cycleClass p x := by
  apply (cycleClass_eq _ _ _).mpr
  exact SameCycle.apply_left SameCycle.rfl

omit [Fintype α] in
lemma mergedClass_step (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b) (x : α) :
    mergedClass p a b ((swap a b * p) x) = mergedClass p a b x := by
  have hne : cycleClass p a ≠ cycleClass p b := mt (cycleClass_eq p a b).mp hab
  change mergedClass p a b (swap a b (p x)) = _
  by_cases hxa : p x = a
  · have hx : cycleClass p x = cycleClass p a := by
      rw [← cycleClass_apply, hxa]
    simp only [mergedClass, hxa, swap_apply_left, ↓reduceIte, hx, hne]
  · by_cases hxb : p x = b
    · have hx : cycleClass p x = cycleClass p b := by
        rw [← cycleClass_apply, hxb]
      simp only [mergedClass, hxb, swap_apply_right, hne, ↓reduceIte, hx]
    · simp only [mergedClass, swap_apply_of_ne_of_ne hxa hxb, cycleClass_apply]

lemma mergedClass_cycle (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b)
    {x y : α} (hxy : (swap a b * p).SameCycle x y) :
    mergedClass p a b x = mergedClass p a b y := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, mergedClass_step p a b hab]
    exact ih

def mergeCycleEquiv (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b) :
    Cycles (swap a b * p) ≃ {c : Cycles p // c ≠ cycleClass p b} where
  toFun := Quotient.lift (fun x => ⟨mergedClass p a b x, by
    have hne : cycleClass p a ≠ cycleClass p b := mt (cycleClass_eq p a b).mp hab
    simp only [mergedClass]
    split_ifs with h <;> assumption⟩)
    (fun _ _ h => Subtype.ext (mergedClass_cycle p a b hab h))
  invFun c := Quotient.map' id (fun _ _ h => sameCycle_swap_mul p a b hab h) c.val
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h x =>
      change Quotient.map' id _ (mergedClass p a b x) = cycleClass (swap a b * p) x
      unfold mergedClass
      split_ifs with hx
      · apply (cycleClass_eq _ _ _).mpr
        exact (swap_mul_sameCycle p a b hab).trans
          (sameCycle_swap_mul p a b hab ((cycleClass_eq _ _ _).mp hx).symm)
      · rfl
  right_inv c := by
    apply Subtype.ext
    rcases c with ⟨c, hc⟩
    induction c using Quotient.inductionOn with
    | h x =>
      change mergedClass p a b x = cycleClass p x
      change cycleClass p x ≠ cycleClass p b at hc
      simp only [mergedClass, hc, ↓reduceIte]

lemma swap_mul_cycles_card (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b) :
    Nat.card (Cycles (swap a b * p)) + 1 = Nat.card (Cycles p) := by
  have h := Fintype.card_congr (mergeCycleEquiv p a b hab)
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h
  have hp : 0 < Fintype.card (Cycles p) := Fintype.card_pos_iff.mpr ⟨cycleClass p a⟩
  simp only [Nat.card_eq_fintype_card]
  omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
attribute [local simp] SameCycle.rfl
variable {α : Type portUniverse4} [Fintype α]

lemma sameCycle_map_quotient {p q : Perm α}
    (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y) :
    Nat.card (Cycles q) ≤ Nat.card (Cycles p) := by
  exact Nat.card_le_card_of_surjective (Quotient.map id (fun _ _ hxy => h hxy))
    (Quotient.map_surjective _ Function.surjective_id)

lemma swap_cycles_card_le (p : Perm α) (a b : α) :
    Nat.card (Cycles (swap a b * p)) ≤ Nat.card (Cycles p) + 1 := by
  let q := swap a b * p
  have hrev : swap a b * q = p := by simp only [← mul_assoc, swap_mul_self, one_mul, q]
  by_cases hab : q.SameCycle a b
  · have href : ∀ {x y}, p.SameCycle x y → q.SameCycle x y := by
      intro x y h
      apply sameCycle_map p q id _ h
      intro x
      have hx : q.SameCycle x (q x) := by simp only [sameCycle_apply_right, SameCycle.rfl]
      have hp : p x = swap a b (q x) := by
        rw [← Perm.mul_apply, hrev]
      rw [hp]
      by_cases hxa : q x = a
      · rw [hxa] at hx
        simpa only [id_eq, hxa, swap_apply_left] using hx.trans hab
      · by_cases hxb : q x = b
        · rw [hxb] at hx
          simpa only [id_eq, hxb, swap_apply_right] using hx.trans hab.symm
        · rwa [swap_apply_of_ne_of_ne hxa hxb]
    exact (sameCycle_map_quotient href).trans (Nat.le_succ _)
  · have h := swap_mul_cycles_card q a b hab
    rw [hrev] at h
    change Nat.card (Cycles q) ≤ _
    omega

lemma cycles_card_le (p : Perm α) : Nat.card (Cycles p) ≤ Fintype.card α := by
  simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_surjective (cycleClass p) Quotient.mk_surjective

lemma cycles_one_card : Nat.card (Cycles (1 : Perm α)) = Fintype.card α := by
  have heq : SameCycle.setoid (1 : Perm α) = ⊥ := by
    ext x y
    exact sameCycle_one
  rw [Cycles, heq]
  exact (Nat.card_congr Setoid.quotientBotEquiv).trans (Nat.card_eq_fintype_card)

lemma exists_cycle_factorization (p : Perm α) :
    ∃ l : List (α × α),
      (l.map fun ab => swap ab.1 ab.2).prod = p ∧
      l.length + Nat.card (Cycles p) = Fintype.card α ∧
      ∀ ab ∈ l, ab.1 ≠ ab.2 ∧ p.SameCycle ab.1 ab.2 := by
  have hmain : ∀ n : ℕ, ∀ p : Perm α,
      Fintype.card α - Nat.card (Cycles p) = n →
      ∃ l : List (α × α),
        (l.map fun ab => swap ab.1 ab.2).prod = p ∧
        l.length + Nat.card (Cycles p) = Fintype.card α ∧
        ∀ ab ∈ l, ab.1 ≠ ab.2 ∧ p.SameCycle ab.1 ab.2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn
      by_cases hp : p = 1
      · subst p
        exact ⟨[], by simp only [List.map_nil, List.prod_nil], by simpa only [List.length_nil, Nat.card_eq_fintype_card, zero_add] using cycles_one_card (α := α), by simp only [List.not_mem_nil, ne_eq, sameCycle_one, not_and_self, imp_self, implies_true]⟩
      · have hex : ∃ a, p a ≠ a := by
          by_contra! h
          exact hp (Equiv.ext h)
        obtain ⟨a, ha⟩ := hex
        have hc := unplug_cycles_card p a ha
        have hle := cycles_card_le (unplug p a)
        have hlt : Fintype.card α - Nat.card (Cycles (unplug p a)) < n := by omega
        obtain ⟨l, hl, hlen, hmem⟩ := ih _ hlt (unplug p a) rfl
        refine ⟨(a, p a) :: l, ?_, ?_, ?_⟩
        · simp only [List.map_cons, List.prod_cons, hl]
          simp only [unplug, ← mul_assoc, swap_mul_self, one_mul]
        · simp only [List.length_cons]
          omega
        · intro ab hab
          rcases List.mem_cons.mp hab with rfl | hab
          · exact ⟨Ne.symm ha, by simp only [sameCycle_apply_right, SameCycle.rfl]⟩
          · exact ⟨(hmem ab hab).1, unplug_sameCycle p a (hmem ab hab).2⟩
  exact hmain _ p rfl

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse5}

def mergeClass (s : Setoid α) (a b x : α) : Quotient s :=
  if Quotient.mk s x = Quotient.mk s b then Quotient.mk s a else Quotient.mk s x

def joinPair (s : Setoid α) (a b : α) : Setoid α := Setoid.ker (mergeClass s a b)

lemma le_joinPair (s : Setoid α) (a b : α) : s ≤ joinPair s a b := by
  intro x y hxy
  change mergeClass s a b x = mergeClass s a b y
  simp only [mergeClass, Quotient.sound hxy]

lemma joinPair_related (s : Setoid α) (a b : α) : (joinPair s a b).r a b := by
  change mergeClass s a b a = mergeClass s a b b
  simp only [mergeClass, ite_self, ↓reduceIte]

lemma joinPair_eq_of_related (s : Setoid α) {a b : α} (hab : s.r a b) :
    joinPair s a b = s := by
  ext x y
  have h : ∀ x, mergeClass s a b x = Quotient.mk s x := by
    intro x
    simp only [mergeClass, ← Quotient.sound hab]
    split_ifs with hx
    · exact hx.symm
    · rfl
  change mergeClass s a b x = mergeClass s a b y ↔ s.r x y
  rw [h, h, Quotient.eq]

lemma joinPair_le (s t : Setoid α) (a b : α) (hst : s ≤ t) (hab : t.r a b) :
    joinPair s a b ≤ t := by
  intro x y hxy
  change mergeClass s a b x = mergeClass s a b y at hxy
  by_cases hx : Quotient.mk s x = Quotient.mk s b
  · by_cases hy : Quotient.mk s y = Quotient.mk s b
    · exact t.iseqv.trans (hst (Quotient.exact hx)) (t.iseqv.symm (hst (Quotient.exact hy)))
    · simp only [mergeClass, hx, hy, ite_true, ite_false] at hxy
      exact t.iseqv.trans (t.iseqv.trans (hst (Quotient.exact hx)) (t.iseqv.symm hab)) (hst (Quotient.exact hxy))
  · by_cases hy : Quotient.mk s y = Quotient.mk s b
    · simp only [mergeClass, hx, hy, ite_true, ite_false] at hxy
      exact t.iseqv.trans (t.iseqv.trans (hst (Quotient.exact hxy)) hab) (t.iseqv.symm (hst (Quotient.exact hy)))
    · simp only [mergeClass, hx, hy, ite_false] at hxy
      exact hst (Quotient.exact hxy)

def joinPairEquiv (s : Setoid α) (a b : α) (hab : ¬ s.r a b) :
    Quotient (joinPair s a b) ≃ {c : Quotient s // c ≠ Quotient.mk s b} where
  toFun := Quotient.lift (fun x => ⟨mergeClass s a b x, by
    have hne : Quotient.mk s a ≠ Quotient.mk s b := fun h => hab (Quotient.exact h)
    simp only [mergeClass]
    split_ifs with hx <;> assumption⟩) (fun _ _ h => Subtype.ext h)
  invFun c := Quotient.map id (fun _ _ h => le_joinPair s a b h) c.val
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h x =>
      change Quotient.map id _ (mergeClass s a b x) = Quotient.mk _ x
      unfold mergeClass
      split_ifs with hx
      · apply Quotient.sound
        exact (joinPair s a b).iseqv.trans (joinPair_related s a b) (le_joinPair s a b (s.iseqv.symm (Quotient.exact hx)))
      · rfl
  right_inv c := by
    rcases c with ⟨c, hc⟩
    apply Subtype.ext
    induction c using Quotient.inductionOn with
    | h x =>
      change mergeClass s a b x = Quotient.mk s x
      simp only [mergeClass, hc, ↓reduceIte]

lemma joinPair_card [Fintype α] (s : Setoid α) (a b : α) (hab : ¬ s.r a b) :
    Nat.card (Quotient (joinPair s a b)) + 1 = Nat.card (Quotient s) := by
  have h := Fintype.card_congr (joinPairEquiv s a b hab)
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h
  have hp : 0 < Fintype.card (Quotient s) := Fintype.card_pos_iff.mpr ⟨Quotient.mk s a⟩
  simp only [Nat.card_eq_fintype_card]
  omega

lemma setoid_swap_related (s : Setoid α) {a b : α} (hab : s.r a b) (x : α) :
    s.r x (swap a b x) := by
  by_cases ha : x = a
  · subst x
    simpa only [swap_apply_left] using hab
  · by_cases hb : x = b
    · subst x
      simpa only [swap_apply_right] using s.iseqv.symm hab
    · rw [swap_apply_of_ne_of_ne ha hb]

lemma setoid_sameCycle_of_step [Fintype α] (s : Setoid α) (p : Perm α)
    (hstep : ∀ x, s.r x (p x)) {x y : α} (hxy : p.SameCycle x y) : s.r x y := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => exact s.iseqv.refl _
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact s.iseqv.trans ih (hstep _)

def edgePartition : List (α × α) → Setoid α
  | [] => ⊥
  | (a, b) :: l => joinPair (edgePartition l) a b

lemma edgePartition_le {l : List (α × α)} {s : Setoid α}
    (h : ∀ ab ∈ l, s.r ab.1 ab.2) : edgePartition l ≤ s := by
  induction l with
  | nil => exact bot_le
  | cons ab l ih =>
    exact joinPair_le _ _ _ _ (ih fun ab hab => h ab (List.mem_cons_of_mem _ hab))
      (h ab List.mem_cons_self)

lemma edgePartition_pair {l : List (α × α)} {ab : α × α} (h : ab ∈ l) :
    (edgePartition l).r ab.1 ab.2 := by
  induction l with
  | nil => simp only [List.not_mem_nil] at h
  | cons cd l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact joinPair_related _ _ _
    · exact le_joinPair _ _ _ (ih h)

lemma edgePartition_prod (l : List (α × α)) (x : α) :
    (edgePartition l).r x ((l.map fun ab => swap ab.1 ab.2).prod x) := by
  induction l with
  | nil => exact (⊥ : Setoid α).iseqv.refl x
  | cons ab l ih =>
    simp only [List.map_cons, List.prod_cons, Perm.mul_apply]
    exact (edgePartition (ab :: l)).iseqv.trans (le_joinPair _ _ _ ih)
      (setoid_swap_related (edgePartition (ab :: l)) (joinPair_related _ _ _) _)

lemma transposition_euler_bound [Fintype α] (l : List (α × α)) :
    Fintype.card α + Nat.card (Cycles (l.map fun ab => swap ab.1 ab.2).prod) ≤
      l.length + 2 * Nat.card (Quotient (edgePartition l)) := by
  induction l with
  | nil =>
    change Fintype.card α + Nat.card (Cycles (1 : Perm α)) ≤
      0 + 2 * Nat.card (Quotient (⊥ : Setoid α))
    rw [cycles_one_card, Nat.card_congr Setoid.quotientBotEquiv, Nat.card_eq_fintype_card]
    omega
  | cons ab l ih =>
    let p := (l.map fun ab => swap ab.1 ab.2).prod
    change Fintype.card α + Nat.card (Cycles (swap ab.1 ab.2 * p)) ≤
      (l.length + 1) + 2 * Nat.card (Quotient (joinPair (edgePartition l) ab.1 ab.2))
    by_cases h : (edgePartition l).r ab.1 ab.2
    · rw [joinPair_eq_of_related _ h]
      have hc := swap_cycles_card_le p ab.1 ab.2
      change Fintype.card α + Nat.card (Cycles p) ≤ _ at ih
      omega
    · have hab : ¬ p.SameCycle ab.1 ab.2 := by
        intro hc
        exact h (setoid_sameCycle_of_step (edgePartition l) p (edgePartition_prod l) hc)
      have hc := swap_mul_cycles_card p ab.1 ab.2 hab
      have hs := joinPair_card (edgePartition l) ab.1 ab.2 h
      change Fintype.card α + Nat.card (Cycles p) ≤ _ at ih
      omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse6} [Fintype α]

lemma quotient_card_antitone {s t : Setoid α} (h : s ≤ t) :
    Nat.card (Quotient t) ≤ Nat.card (Quotient s) := by
  exact Nat.card_le_card_of_surjective (Quotient.map id (fun _ _ hxy => h hxy))
    (Quotient.map_surjective _ Function.surjective_id)

def Ribbon.components (R : Ribbon α) : Setoid α :=
  SameCycle.setoid R.black ⊔ SameCycle.setoid R.white

omit [Fintype α] in
lemma cycles_inv_card (p : Perm α) : Nat.card (Cycles p⁻¹) = Nat.card (Cycles p) := by
  have h : SameCycle.setoid p⁻¹ = SameCycle.setoid p := by
    ext a b
    exact sameCycle_inv
  unfold Cycles
  rw [h]

theorem Ribbon.euler_le (R : Ribbon α) :
    Nat.card (Cycles R.black) + Nat.card (Cycles R.white) + Nat.card (Cycles R.face) ≤
      Fintype.card α + 2 * Nat.card (Quotient R.components) := by
  obtain ⟨lb, hb, hblen, _⟩ := exists_cycle_factorization R.black
  obtain ⟨lw, hw, hwlen, _⟩ := exists_cycle_factorization R.white
  obtain ⟨lf, hf, hflen, _⟩ := exists_cycle_factorization R.face⁻¹
  rw [cycles_inv_card] at hflen
  let l := lw ++ lb ++ lf
  have hl : (l.map fun ab => swap ab.1 ab.2).prod = 1 := by
    simp only [l, List.map_append, List.prod_append, hb, hw, hf]
    change R.face * R.face⁻¹ = 1
    exact mul_inv_cancel _
  have hbl : edgePartition lb ≤ edgePartition l := by
    apply edgePartition_le
    intro ab hab
    apply edgePartition_pair
    simp only [List.append_assoc, List.mem_append, hab, true_or, or_true, l]
  have hwl : edgePartition lw ≤ edgePartition l := by
    apply edgePartition_le
    intro ab hab
    apply edgePartition_pair
    simp only [List.append_assoc, List.mem_append, hab, true_or, l]
  have hcomp : R.components ≤ edgePartition l := by
    apply sup_le
    · intro x y hxy
      apply setoid_sameCycle_of_step (edgePartition l) R.black _ hxy
      intro x
      rw [← hb]
      exact hbl (edgePartition_prod lb x)
    · intro x y hxy
      apply setoid_sameCycle_of_step (edgePartition l) R.white _ hxy
      intro x
      rw [← hw]
      exact hwl (edgePartition_prod lw x)
  have hc := quotient_card_antitone hcomp
  have hbound := transposition_euler_bound l
  rw [hl, cycles_one_card] at hbound
  have hlen : l.length = lw.length + lb.length + lf.length := by simp only [List.append_assoc, List.length_append, Nat.add_assoc, Nat.add_left_cancel_iff, l]
  omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse7}

def restrictQuotient (s : Setoid α) (P : α → Prop) :
    Quotient (s.comap (Subtype.val : {x // P x} → α)) → Quotient s :=
  Quotient.map Subtype.val (fun _ _ h => h)

lemma restrictQuotient_injective (s : Setoid α) (P : α → Prop) :
    Function.Injective (restrictQuotient s P) := by
  intro x y
  induction x, y using Quotient.inductionOn₂ with
  | h x y =>
    intro h
    change Quotient.mk s x.val = Quotient.mk s y.val at h
    apply Quotient.sound
    change s.r x.val y.val
    exact Quotient.exact h

def quotientRestrictSumEquiv (s : Setoid α) (P : α → Prop)
    (hP : ∀ {x y}, s.r x y → (P x ↔ P y)) :
    (Quotient (s.comap (Subtype.val : {x // P x} → α)) ⊕
      Quotient (s.comap (Subtype.val : {x // ¬ P x} → α))) ≃ Quotient s :=
  Equiv.ofBijective (Sum.elim (restrictQuotient s P) (restrictQuotient s (fun x => ¬ P x))) (by
    constructor
    · intro a b hab
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (restrictQuotient_injective s P hab)
        | inr b =>
          induction a, b using Quotient.inductionOn₂ with
          | h a b => exact (b.prop ((hP (Quotient.exact hab)).mp a.prop)).elim
      | inr a =>
        cases b with
        | inl b =>
          induction a, b using Quotient.inductionOn₂ with
          | h a b => exact (a.prop ((hP (Quotient.exact hab)).mpr b.prop)).elim
        | inr b => exact congrArg Sum.inr (restrictQuotient_injective s _ hab)
    · intro c
      induction c using Quotient.inductionOn with
      | h x =>
        by_cases hx : P x
        · exact ⟨Sum.inl (Quotient.mk _ ⟨x, hx⟩), rfl⟩
        · exact ⟨Sum.inr (Quotient.mk _ ⟨x, hx⟩), rfl⟩)

lemma quotient_restrict_card_split [Fintype α] (s : Setoid α) (P : α → Prop)
    (hP : ∀ {x y}, s.r x y → (P x ↔ P y)) :
    Nat.card (Quotient (s.comap (Subtype.val : {x // P x} → α))) +
      Nat.card (Quotient (s.comap (Subtype.val : {x // ¬ P x} → α))) =
      Nat.card (Quotient s) := by
  simpa only [Nat.card_sum] using Nat.card_congr (quotientRestrictSumEquiv s P hP)

variable [Fintype α]

lemma perm_invariant_cycle (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x)
    {x y : α} (hxy : p.SameCycle x y) : P x ↔ P y := by
  exact Iff.of_eq (setoid_sameCycle_of_step (Setoid.ker P) p
    (fun x => propext (hP x).symm) hxy)

omit [Fintype α] in
lemma subtype_cycles_setoid (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x) :
    SameCycle.setoid (p.subtypePerm hP) =
      (SameCycle.setoid p).comap (Subtype.val : {x // P x} → α) := by
  ext x y
  exact sameCycle_subtypePerm

lemma cycles_restrict_card_split (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x) :
    Nat.card (Cycles (p.subtypePerm hP)) +
      Nat.card (Cycles (p.subtypePerm (p := fun x => ¬ P x) fun x => not_congr (hP x))) = Nat.card (Cycles p) := by
  unfold Cycles
  rw [subtype_cycles_setoid, subtype_cycles_setoid]
  exact quotient_restrict_card_split _ P (perm_invariant_cycle p P hP)

def Ribbon.restrict (R : Ribbon α) (P : α → Prop)
    (hb : ∀ x, P (R.black x) ↔ P x) (hw : ∀ x, P (R.white x) ↔ P x) :
    Ribbon {x // P x} where
  black := R.black.subtypePerm hb
  white := R.white.subtypePerm hw

lemma Ribbon.invariant_components (R : Ribbon α) (P : α → Prop)
    (hb : ∀ x, P (R.black x) ↔ P x) (hw : ∀ x, P (R.white x) ↔ P x)
    {x y : α} (hxy : R.components.r x y) : P x ↔ P y := by
  have h : R.components ≤ Setoid.ker P := by
    apply sup_le
    · exact fun _ _ h => propext (perm_invariant_cycle R.black P hb h)
    · exact fun _ _ h => propext (perm_invariant_cycle R.white P hw h)
  exact Iff.of_eq (h hxy)

lemma Ribbon.restrict_components (R : Ribbon α) (P : α → Prop) (hb hw) :
    (R.restrict P hb hw).components =
      R.components.comap (Subtype.val : {x // P x} → α) := by
  apply le_antisymm
  · apply sup_le
    · intro x y h
      exact (show SameCycle.setoid R.black ≤ R.components from le_sup_left) ((sameCycle_subtypePerm (h := hb)).mp h)
    · intro x y h
      exact (show SameCycle.setoid R.white ≤ R.components from le_sup_right) ((sameCycle_subtypePerm (h := hw)).mp h)
  · intro x y hxy
    change R.components.r x.val y.val at hxy
    have hmain : ∀ {a b : α}, R.components.r a b → ∀ (ha : P a) (hb' : P b),
        (R.restrict P hb hw).components.r ⟨a, ha⟩ ⟨b, hb'⟩ := by
      intro a b h
      rw [Ribbon.components, Setoid.sup_def] at h
      change Relation.EqvGen (fun a b => R.black.SameCycle a b ∨ R.white.SameCycle a b) a b at h
      induction h with
      | rel a b hab =>
        intro ha hb'
        rcases hab with hab | hab
        · exact (show SameCycle.setoid (R.restrict P hb hw).black ≤ (R.restrict P hb hw).components from le_sup_left) ((sameCycle_subtypePerm (h := hb)).mpr hab)
        · exact (show SameCycle.setoid (R.restrict P hb hw).white ≤ (R.restrict P hb hw).components from le_sup_right) ((sameCycle_subtypePerm (h := hw)).mpr hab)
      | refl a => exact fun _ _ => (R.restrict P hb hw).components.iseqv.refl _
      | symm a b hab ih =>
        intro ha hb'
        exact (R.restrict P hb hw).components.iseqv.symm (ih hb' ha)
      | trans a b c hab hbc ihab ihbc =>
        intro ha hc
        have hab' : R.components.r a b := by
          rw [Ribbon.components, Setoid.sup_def]
          exact hab
        have hb' : P b := (R.invariant_components P hb hw hab').mp ha
        exact (R.restrict P hb hw).components.iseqv.trans (ihab ha hb') (ihbc hb' hc)
    exact hmain hxy x.prop y.prop

def Ribbon.GenusZero (R : Ribbon α) : Prop :=
  Nat.card (Cycles R.black) + Nat.card (Cycles R.white) + Nat.card (Cycles R.face) =
    Fintype.card α + 2 * Nat.card (Quotient R.components)

lemma Ribbon.planar_restrict (R : Ribbon α) (hR : R.GenusZero) (P : α → Prop) (hb hw) :
    (R.restrict P hb hw).GenusZero := by
  let S := R.restrict P hb hw
  let T := R.restrict (fun x => ¬ P x) (fun x => not_congr (hb x)) (fun x => not_congr (hw x))
  have hs := S.euler_le
  have ht := T.euler_le
  have hbc := cycles_restrict_card_split R.black P hb
  have hwc := cycles_restrict_card_split R.white P hw
  have hfc := cycles_restrict_card_split R.face P (fun x => (hw _).trans (hb x))
  have hcc := quotient_restrict_card_split R.components P (R.invariant_components P hb hw)
  rw [← R.restrict_components P hb hw,
    ← R.restrict_components (fun x => ¬ P x) (fun x => not_congr (hb x))
      (fun x => not_congr (hw x))] at hcc
  have hec : Fintype.card {x // P x} + Fintype.card {x // ¬ P x} = Fintype.card α := by
    have h := Fintype.card_subtype_compl P
    have hle := Fintype.card_subtype_le P
    omega
  change Nat.card (Cycles S.black) + Nat.card (Cycles T.black) = _ at hbc
  change Nat.card (Cycles S.white) + Nat.card (Cycles T.white) = _ at hwc
  change Nat.card (Cycles S.face) + Nat.card (Cycles T.face) = _ at hfc
  change Nat.card (Quotient S.components) + Nat.card (Quotient T.components) = _ at hcc
  unfold Ribbon.GenusZero at hR ⊢
  change Nat.card (Cycles S.black) + Nat.card (Cycles S.white) + Nat.card (Cycles S.face) =
    Fintype.card {x // P x} + 2 * Nat.card (Quotient S.components)
  omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
attribute [local simp] SameCycle.rfl
variable {α : Type portUniverse8} [Fintype α]

omit [Fintype α] in
lemma Ribbon.black_step (R : Ribbon α) (x : α) : R.components.r x (R.black x) :=
  (show SameCycle.setoid R.black ≤ R.components from le_sup_left) (show R.black.SameCycle x (R.black x) from SameCycle.apply_right SameCycle.rfl)

omit [Fintype α] in
lemma Ribbon.white_step (R : Ribbon α) (x : α) : R.components.r x (R.white x) :=
  (show SameCycle.setoid R.white ≤ R.components from le_sup_right) (show R.white.SameCycle x (R.white x) from SameCycle.apply_right SameCycle.rfl)

lemma Ribbon.components_le_of_steps (R : Ribbon α) (s : Setoid α)
    (hb : ∀ x, s.r x (R.black x)) (hw : ∀ x, s.r x (R.white x)) : R.components ≤ s := by
  exact sup_le (fun _ _ h => setoid_sameCycle_of_step s R.black hb h)
    (fun _ _ h => setoid_sameCycle_of_step s R.white hw h)

omit [Fintype α] in
lemma Ribbon.black_component_invariant (R : Ribbon α) (a x : α) :
    R.components.r (R.black x) a ↔ R.components.r x a := by
  constructor
  · exact R.components.iseqv.trans (R.black_step x)
  · exact R.components.iseqv.trans (R.components.iseqv.symm (R.black_step x))

omit [Fintype α] in
lemma Ribbon.white_component_invariant (R : Ribbon α) (a x : α) :
    R.components.r (R.white x) a ↔ R.components.r x a := by
  constructor
  · exact R.components.iseqv.trans (R.white_step x)
  · exact R.components.iseqv.trans (R.components.iseqv.symm (R.white_step x))

omit [Fintype α] in
lemma joinPair_left_iff (s : Setoid α) (a b y : α) :
    (joinPair s a b).r a y ↔ s.r a y ∨ s.r b y := by
  change mergeClass s a b a = mergeClass s a b y ↔ _
  have ha : mergeClass s a b a = Quotient.mk s a := by simp only [mergeClass, ite_self]
  rw [ha]
  by_cases hy : Quotient.mk s y = Quotient.mk s b
  · simp only [mergeClass, hy, ite_true, true_iff]
    exact Or.inr (s.iseqv.symm (Quotient.exact hy))
  · simp only [mergeClass, hy, ite_false, Quotient.eq]
    exact or_iff_left (fun h => hy (Quotient.sound (s.iseqv.symm h))) |>.symm

def Ribbon.detach (R : Ribbon α) (a : α) : Ribbon α where
  black := unplug R.black a
  white := unplug R.white a

omit [Fintype α] in
lemma Ribbon.detach_fixed_black (R : Ribbon α) (a : α) : (R.detach a).black a = a :=
  unplug_fixed _ _
omit [Fintype α] in
lemma Ribbon.detach_fixed_white (R : Ribbon α) (a : α) : (R.detach a).white a = a :=
  unplug_fixed _ _

lemma Ribbon.detach_isolated (R : Ribbon α) (a : α) {x : α}
    (h : (R.detach a).components.r a x) : x = a := by
  have hb : ∀ x, (R.detach a).black x = a ↔ x = a := by
    intro x
    constructor
    · intro h
      apply (R.detach a).black.injective
      simpa only [R.detach_fixed_black] using h
    · intro hx
      simpa only [hx] using R.detach_fixed_black a
  have hw : ∀ x, (R.detach a).white x = a ↔ x = a := by
    intro x
    constructor
    · intro h
      apply (R.detach a).white.injective
      simpa only [R.detach_fixed_white] using h
    · intro hx
      simpa only [hx] using R.detach_fixed_white a
  exact ((R.detach a).invariant_components (fun x => x = a) hb hw h).mp rfl

lemma Ribbon.detach_components_le (R : Ribbon α) (a : α) :
    (R.detach a).components ≤ R.components := by
  apply sup_le
  · exact fun _ _ h => (show SameCycle.setoid R.black ≤ R.components from le_sup_left)
      (unplug_sameCycle R.black a h)
  · exact fun _ _ h => (show SameCycle.setoid R.white ≤ R.components from le_sup_right)
      (unplug_sameCycle R.white a h)

lemma Ribbon.components_detach (R : Ribbon α) (a : α) :
    R.components = joinPair (joinPair (R.detach a).components a (R.black a)) a (R.white a) := by
  let s := (R.detach a).components
  let t := joinPair (joinPair s a (R.black a)) a (R.white a)
  apply le_antisymm
  · apply R.components_le_of_steps t
    · intro x
      have hstep : t.r x ((R.detach a).black x) :=
        le_joinPair _ _ _ (le_joinPair _ _ _ ((R.detach a).black_step x))
      have hab : t.r a (R.black a) := le_joinPair _ _ _ (joinPair_related _ _ _)
      have hback : swap a (R.black a) ((R.detach a).black x) = R.black x := by
        simp only [detach, unplug, coe_mul, Function.comp_apply, swap_apply_self]
      rw [← hback]
      exact t.iseqv.trans hstep (setoid_swap_related t hab _)
    · intro x
      have hstep : t.r x ((R.detach a).white x) :=
        le_joinPair _ _ _ (le_joinPair _ _ _ ((R.detach a).white_step x))
      have hab : t.r a (R.white a) := joinPair_related _ _ _
      have hback : swap a (R.white a) ((R.detach a).white x) = R.white x := by
        simp only [detach, unplug, coe_mul, Function.comp_apply, swap_apply_self]
      rw [← hback]
      exact t.iseqv.trans hstep (setoid_swap_related t hab _)
  · apply joinPair_le
    · exact joinPair_le _ _ _ _ (R.detach_components_le a) (R.black_step a)
    · exact R.white_step a

omit [Fintype α] in
lemma Ribbon.detach_face (R : Ribbon α) (a : α) :
    (R.detach a).face = swap a (R.white a) * swap (R.white a) (R.face a) * R.face := by
  simp only [Ribbon.detach, Ribbon.face, unplug, mul_assoc]
  rw [← mul_assoc R.white (swap a (R.black a)), mul_swap_eq_swap_mul]
  simp only [Perm.mul_apply, mul_assoc]

omit [Fintype α] in
lemma Ribbon.detach_face_of_face_fixed (R : Ribbon α) (a : α) (ha : R.face a = a) :
    (R.detach a).face = R.face := by
  rw [R.detach_face, ha, swap_comm (R.white a) a]
  simp only [swap_mul_self, one_mul]

omit [Fintype α] in
lemma Ribbon.detach_face_unplug (R : Ribbon α) (a : α)
    (hw : R.white a ≠ a) (hf : R.face a ≠ a) :
    (R.detach a).face = swap (R.white a) (R.face a) * unplug R.face a := by
  rw [R.detach_face, swap_mul_eq_mul_swap]
  have ha : swap (R.white a) (R.face a) a = a := swap_apply_of_ne_of_ne hw.symm hf.symm
  simp only [swap_inv, ha, swap_apply_left, unplug, mul_assoc]

lemma Ribbon.detach_face_card_le (R : Ribbon α) (a : α) (hw : R.white a ≠ a) :
    Nat.card (Cycles R.face) ≤ Nat.card (Cycles (R.detach a).face) := by
  by_cases hf : R.face a = a
  · rw [R.detach_face_of_face_fixed a hf]
  · have h := swap_cycles_card_le (R.detach a).face (R.white a) (R.face a)
    rw [R.detach_face_unplug a hw hf] at h
    simp only [← mul_assoc, swap_mul_self, one_mul] at h
    have hc := unplug_cycles_card R.face a hf
    rw [R.detach_face_unplug a hw hf]
    omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse9} [Fintype α]

omit [Fintype α] in
lemma Ribbon.face_step (R : Ribbon α) (x : α) : R.components.r x (R.face x) :=
  R.components.iseqv.trans (R.black_step x) (R.white_step (R.black x))

lemma Ribbon.sameCycle_face_components (R : Ribbon α) {x y : α} (h : R.face.SameCycle x y) :
    R.components.r x y := setoid_sameCycle_of_step R.components R.face R.face_step h

lemma Ribbon.detach_components_card (R : Ribbon α) (a : α)
    (hb : R.black a ≠ a) (hw : R.white a ≠ a) :
    Nat.card (Quotient (R.detach a).components) = Nat.card (Quotient R.components) +
      if (R.detach a).components.r (R.black a) (R.white a) then 1 else 2 := by
  let s := (R.detach a).components
  let t := joinPair s a (R.black a)
  have hb' : ¬ s.r a (R.black a) := fun h => hb (R.detach_isolated a h)
  have hw' : ¬ s.r a (R.white a) := fun h => hw (R.detach_isolated a h)
  have ht : Nat.card (Quotient t) + 1 = Nat.card (Quotient s) := joinPair_card s _ _ hb'
  have heq : R.components = joinPair t a (R.white a) := R.components_detach a
  by_cases h : s.r (R.black a) (R.white a)
  · have h' : t.r a (R.white a) := (joinPair_left_iff s _ _ _).mpr (Or.inr h)
    rw [joinPair_eq_of_related _ h'] at heq
    change Nat.card (Quotient s) = Nat.card (Quotient R.components) + if s.r (R.black a) (R.white a) then 1 else 2
    simp only [h, ite_true, heq]
    omega
  · have h' : ¬ t.r a (R.white a) := by
      rw [joinPair_left_iff]
      exact not_or.mpr ⟨hw', h⟩
    have ht' := joinPair_card t a (R.white a) h'
    rw [← heq] at ht'
    change Nat.card (Quotient s) = Nat.card (Quotient R.components) + if s.r (R.black a) (R.white a) then 1 else 2
    simp only [h, ite_false]
    omega

lemma Ribbon.detach_components_card_black_fixed (R : Ribbon α) (a : α)
    (hb : R.black a = a) (hw : R.white a ≠ a) :
    Nat.card (Quotient (R.detach a).components) = Nat.card (Quotient R.components) + 1 := by
  have hn : ¬ (R.detach a).components.r a (R.white a) := fun h => hw (R.detach_isolated a h)
  have heq := R.components_detach a
  rw [hb, joinPair_eq_of_related _ ((R.detach a).components.iseqv.refl a)] at heq
  have hc := joinPair_card (R.detach a).components a (R.white a) hn
  rw [← heq] at hc
  omega

lemma Ribbon.detach_components_card_white_fixed (R : Ribbon α) (a : α)
    (hb : R.black a ≠ a) (hw : R.white a = a) :
    Nat.card (Quotient (R.detach a).components) = Nat.card (Quotient R.components) + 1 := by
  have hn : ¬ (R.detach a).components.r a (R.black a) := fun h => hb (R.detach_isolated a h)
  have heq := R.components_detach a
  rw [hw, joinPair_eq_of_related _ ((joinPair (R.detach a).components a (R.black a)).iseqv.refl a)] at heq
  have hc := joinPair_card (R.detach a).components a (R.black a) hn
  rw [← heq] at hc
  omega

omit [Fintype α] in
lemma Ribbon.detach_face_black_fixed (R : Ribbon α) (a : α) (hb : R.black a = a) :
    (R.detach a).face = unplug R.face a := by
  rw [R.detach_face]
  have hf : R.face a = R.white a := by simp only [face, coe_mul, Function.comp_apply, hb]
  simp only [hf, swap_self, unplug, mul_left_inj, mul_eq_left]
  rfl

omit [Fintype α] in
lemma Ribbon.detach_face_white_fixed (R : Ribbon α) (a : α) (hw : R.white a = a) :
    (R.detach a).face = unplug R.face a := by
  rw [R.detach_face, hw]
  simp only [swap_self, unplug, mul_left_inj, mul_eq_right]
  rfl

lemma Ribbon.detach_face_card_separating (R : Ribbon α) (a : α)
    (hb : R.black a ≠ a) (hw : R.white a ≠ a)
    (hsep : ¬ (R.detach a).components.r (R.black a) (R.white a)) :
    Nat.card (Cycles (R.detach a).face) = Nat.card (Cycles R.face) + 2 := by
  have hf : R.face a ≠ a := by
    intro hf
    have hs : (R.detach a).white (R.black a) = R.white a := by
      change swap a (R.white a) (R.face a) = R.white a
      simp only [hf, swap_apply_left]
    exact hsep (hs ▸ (R.detach a).white_step (R.black a))
  have hs : (R.detach a).white (R.black a) = R.face a := by
    change swap a (R.white a) (R.face a) = R.face a
    exact swap_apply_of_ne_of_ne hf (R.white.injective.ne hb)
  have hnot : ¬ (R.detach a).face.SameCycle (R.white a) (R.face a) := by
    intro h
    have hc := (R.detach a).sameCycle_face_components h
    have hs' := (R.detach a).white_step (R.black a)
    rw [hs] at hs'
    exact hsep ((R.detach a).components.iseqv.trans hs'
      ((R.detach a).components.iseqv.symm hc))
  have hcard := swap_mul_cycles_card (R.detach a).face (R.white a) (R.face a) hnot
  have heq : swap (R.white a) (R.face a) * (R.detach a).face = unplug R.face a := by
    rw [R.detach_face_unplug a hw hf]
    simp only [← mul_assoc, swap_mul_self, one_mul]
  rw [heq, unplug_cycles_card R.face a hf] at hcard
  omega

theorem Ribbon.genusZero_detach (R : Ribbon α) (hR : R.GenusZero) (a : α) :
    (R.detach a).GenusZero := by
  by_cases hb : R.black a = a
  · have hblack : (R.detach a).black = R.black := by
      simp only [detach, unplug, hb, swap_self, mul_eq_right]
      rfl
    by_cases hw : R.white a = a
    · have heq : R.detach a = R := by
        cases R
        simp_all [Ribbon.detach, unplug]
      rwa [heq]
    · have hwc := unplug_cycles_card R.white a hw
      have hcc := R.detach_components_card_black_fixed a hb hw
      have hf : R.face a ≠ a := by simpa only [face, coe_mul, Function.comp_apply, hb, ne_eq] using hw
      have hfc := unplug_cycles_card R.face a hf
      rw [← R.detach_face_black_fixed a hb] at hfc
      change Nat.card (Cycles (R.detach a).white) = _ at hwc
      unfold Ribbon.GenusZero at hR ⊢
      rw [hblack]
      omega
  · have hbc := unplug_cycles_card R.black a hb
    change Nat.card (Cycles (R.detach a).black) = _ at hbc
    by_cases hw : R.white a = a
    · have hwhite : (R.detach a).white = R.white := by
        simp only [detach, unplug, hw, swap_self, mul_eq_right]
        rfl
      have hcc := R.detach_components_card_white_fixed a hb hw
      have hf : R.face a ≠ a := by
        intro hf
        apply hb
        apply R.white.injective
        simpa only [hw, face, coe_mul, Function.comp_apply] using hf
      have hfc := unplug_cycles_card R.face a hf
      rw [← R.detach_face_white_fixed a hw] at hfc
      unfold Ribbon.GenusZero at hR ⊢
      rw [hwhite]
      omega
    · have hwc := unplug_cycles_card R.white a hw
      change Nat.card (Cycles (R.detach a).white) = _ at hwc
      have hcc := R.detach_components_card a hb hw
      by_cases hs : (R.detach a).components.r (R.black a) (R.white a)
      · rw [if_pos hs] at hcc
        have hfc := R.detach_face_card_le a hw
        have hbound := (R.detach a).euler_le
        unfold Ribbon.GenusZero at hR ⊢
        omega
      · rw [if_neg hs] at hcc
        have hfc := R.detach_face_card_separating a hb hw hs
        unfold Ribbon.GenusZero at hR ⊢
        omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
attribute [local simp] SameCycle.rfl
variable {α : Type portUniverse10} {V : Type portUniverse11} [Fintype α]

lemma Ribbon.mergeWhite_components (R : Ribbon α) (a : α)
    (ha : ¬ R.white.SameCycle a (R.black a)) : (R.mergeWhite a).components = R.components := by
  have hn : ¬ R.white.SameCycle a (R.face a) := by simpa only [face, coe_mul, Function.comp_apply, sameCycle_apply_right] using ha
  apply le_antisymm
  · apply (R.mergeWhite a).components_le_of_steps
    · exact R.black_step
    · intro x
      exact R.components.iseqv.trans (R.white_step x)
        (setoid_swap_related R.components (R.face_step a) (R.white x))
  · apply sup_le
    · exact le_sup_left
    · intro x y h
      exact (show SameCycle.setoid (R.mergeWhite a).white ≤ (R.mergeWhite a).components
        from le_sup_right) (sameCycle_swap_mul R.white a (R.face a) hn h)

lemma Ribbon.genusZero_mergeWhite (R : Ribbon α) (hR : R.GenusZero) (a : α)
    (ha : ¬ R.white.SameCycle a (R.black a)) : (R.mergeWhite a).GenusZero := by
  have hn : ¬ R.white.SameCycle a (R.face a) := by simpa only [face, coe_mul, Function.comp_apply, sameCycle_apply_right] using ha
  have hne : R.face a ≠ a := by intro h; exact hn (by rw [h])
  have hw := swap_mul_cycles_card R.white a (R.face a) hn
  have hf := unplug_cycles_card R.face a hne
  unfold Ribbon.GenusZero at *
  rw [R.mergeWhite_components a ha, mergeWhite_face]
  change Nat.card (Cycles R.black) + Nat.card (Cycles (swap a (R.face a) * R.white)) +
    Nat.card (Cycles (unplug R.face a)) = _
  omega

def Ribbon.mergeBlack (R : Ribbon α) (a : α) : Ribbon α where
  black := swap a (R.black (R.white a)) * R.black
  white := R.white

omit [Fintype α] in
lemma Ribbon.mergeBlack_face (R : Ribbon α) (a : α) :
    (R.mergeBlack a).face = unplug R.face (R.white a) := by
  simp only [Ribbon.mergeBlack, Ribbon.face, unplug, ← mul_assoc]
  rw [mul_swap_eq_swap_mul]
  rfl

lemma Ribbon.mergeBlack_components (R : Ribbon α) (a : α)
    (ha : ¬ R.black.SameCycle a (R.white a)) : (R.mergeBlack a).components = R.components := by
  have hn : ¬ R.black.SameCycle a (R.black (R.white a)) := by simpa only [sameCycle_apply_right] using ha
  apply le_antisymm
  · apply (R.mergeBlack a).components_le_of_steps
    · intro x
      exact R.components.iseqv.trans (R.black_step x)
        (setoid_swap_related R.components
          (R.components.iseqv.trans (R.white_step a) (R.black_step (R.white a))) (R.black x))
    · exact R.white_step
  · apply sup_le
    · intro x y h
      exact (show SameCycle.setoid (R.mergeBlack a).black ≤ (R.mergeBlack a).components
        from le_sup_left) (sameCycle_swap_mul R.black a (R.black (R.white a)) hn h)
    · exact le_sup_right

lemma Ribbon.genusZero_mergeBlack (R : Ribbon α) (hR : R.GenusZero) (a : α)
    (ha : ¬ R.black.SameCycle a (R.white a)) : (R.mergeBlack a).GenusZero := by
  have hn : ¬ R.black.SameCycle a (R.black (R.white a)) := by simpa only [sameCycle_apply_right] using ha
  have hne : R.face (R.white a) ≠ R.white a := by
    intro h
    have h' : R.black (R.white a) = a := R.white.injective h
    exact hn (by rw [h'])
  have hb := swap_mul_cycles_card R.black a (R.black (R.white a)) hn
  have hf := unplug_cycles_card R.face (R.white a) hne
  unfold Ribbon.GenusZero at *
  rw [R.mergeBlack_components a ha, R.mergeBlack_face]
  change Nat.card (Cycles (swap a (R.black (R.white a)) * R.black)) +
    Nat.card (Cycles R.white) + Nat.card (Cycles (unplug R.face (R.white a))) = _
  omega

omit [Fintype α] in
lemma label_swap (f : α → V) (a b : α) (hab : f a = f b) (x : α) :
    f (swap a b x) = f x := by
  by_cases hxa : x = a
  · subst x
    simpa only [swap_apply_left] using hab.symm
  · by_cases hxb : x = b
    · subst x
      simpa only [swap_apply_right] using hab
    · rw [swap_apply_of_ne_of_ne hxa hxb]

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse12} [Fintype α]

lemma sameCycle_after_swap {p : Perm α} {a b x y : α} (hab : p.SameCycle a b)
    (hxy : (swap a b * p).SameCycle x y) : p.SameCycle x y := by
  apply setoid_sameCycle_of_step (SameCycle.setoid p) (swap a b * p) _ hxy
  intro z
  exact (SameCycle.apply_right SameCycle.rfl).trans
    (setoid_swap_related (SameCycle.setoid p) hab (p z))

lemma sign_eq_cycles (p : Perm α) :
    sign p = (-1 : ℤˣ) ^ (Fintype.card α - Nat.card (Cycles p)) := by
  classical
  obtain ⟨l, hl, hlen, hmem⟩ := exists_cycle_factorization p
  have hs := sign_prod_list_swap (l := l.map fun ab => swap ab.1 ab.2) (by
    intro g hg
    obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hg
    exact ⟨ab.1, ab.2, (hmem ab hab).1, rfl⟩)
  rw [hl, List.length_map] at hs
  have hn : Fintype.card α - Nat.card (Cycles p) = l.length := by omega
  rwa [hn]

lemma not_sameCycle_swap_of_sameCycle (p : Perm α) (a b : α)
    (hne : a ≠ b) (hab : p.SameCycle a b) : ¬ (swap a b * p).SameCycle a b := by
  classical
  intro hq
  let q := swap a b * p
  have hrev : swap a b * q = p := by simp only [← mul_assoc, swap_mul_self, one_mul, q]
  have heq : SameCycle.setoid p = SameCycle.setoid q := by
    ext x y
    constructor
    · intro h
      apply sameCycle_after_swap hq
      rwa [hrev]
    · exact sameCycle_after_swap hab
  have hc : Nat.card (Cycles p) = Nat.card (Cycles q) := by rw [Cycles, heq]
  have hs : sign p = sign q := by rw [sign_eq_cycles, sign_eq_cycles, hc]
  have hsign : (-1 : ℤˣ) = 1 := by
    have := hs
    change sign p = sign (swap a b * p) at this
    rw [Perm.sign_mul, sign_swap hne] at this
    exact mul_right_cancel (b := sign p) (by simpa only [neg_mul, one_mul, neg_units_ne_self] using this.symm)
  norm_num at hsign

lemma swap_mul_cycles_card_split (p : Perm α) (a b : α)
    (hne : a ≠ b) (hab : p.SameCycle a b) :
    Nat.card (Cycles (swap a b * p)) = Nat.card (Cycles p) + 1 := by
  have h := swap_mul_cycles_card (swap a b * p) a b
    (not_sameCycle_swap_of_sameCycle p a b hne hab)
  simpa only [Nat.card_eq_fintype_card, ← mul_assoc, swap_mul_self, one_mul] using h.symm

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse13} [Fintype α]

def Ribbon.swapBlack (R : Ribbon α) (a b : α) : Ribbon α :=
  ⟨swap a b * R.black, R.white⟩

omit [Fintype α] in
lemma Ribbon.swapBlack_twice (R : Ribbon α) (a b : α) :
    (R.swapBlack a b).swapBlack a b = R := by
  cases R
  simp only [swapBlack, ← mul_assoc, swap_mul_self, one_mul]

omit [Fintype α] in
lemma Ribbon.swapBlack_face (R : Ribbon α) (a b : α) :
    (R.swapBlack a b).face = swap (R.white a) (R.white b) * R.face := by
  simp only [Ribbon.face, Ribbon.swapBlack, ← mul_assoc]
  rw [mul_swap_eq_swap_mul]

lemma Ribbon.swapBlack_components_merge (R : Ribbon α) (a b : α)
    (hab : ¬ R.black.SameCycle a b) :
    (R.swapBlack a b).components = joinPair R.components a b := by
  apply le_antisymm
  · apply (R.swapBlack a b).components_le_of_steps
    · intro x
      exact (joinPair R.components a b).iseqv.trans
        (le_joinPair _ _ _ (R.black_step x))
        (setoid_swap_related _ (joinPair_related _ _ _) _)
    · intro x
      exact le_joinPair _ _ _ (R.white_step x)
  · apply joinPair_le
    · apply sup_le
      · intro x y hxy
        exact (show SameCycle.setoid (R.swapBlack a b).black ≤
            (R.swapBlack a b).components from le_sup_left)
          (sameCycle_swap_mul R.black a b hab hxy)
      · exact le_sup_right
    · exact (show SameCycle.setoid (R.swapBlack a b).black ≤
          (R.swapBlack a b).components from le_sup_left)
        (swap_mul_sameCycle R.black a b hab)

omit [Fintype α] in
lemma Ribbon.not_blackCycle_of_not_component (R : Ribbon α) {a b : α}
    (h : ¬ R.components.r a b) : ¬ R.black.SameCycle a b :=
  fun hab => h ((show SameCycle.setoid R.black ≤ R.components from le_sup_left) hab)

lemma Ribbon.not_white_faceCycle_of_not_component (R : Ribbon α) {a b : α}
    (h : ¬ R.components.r a b) : ¬ R.face.SameCycle (R.white a) (R.white b) := by
  intro hab
  exact h (R.components.iseqv.trans (R.white_step a)
    (R.components.iseqv.trans (R.sameCycle_face_components hab)
      (R.components.iseqv.symm (R.white_step b))))

lemma Ribbon.genusZero_swapBlack_merge (R : Ribbon α) (hR : R.GenusZero) (a b : α)
    (hab : ¬ R.components.r a b) : (R.swapBlack a b).GenusZero := by
  have hb := R.not_blackCycle_of_not_component hab
  have hbc := swap_mul_cycles_card R.black a b hb
  have hfc := swap_mul_cycles_card R.face (R.white a) (R.white b)
    (R.not_white_faceCycle_of_not_component hab)
  have hcc := joinPair_card R.components a b hab
  rw [← R.swapBlack_components_merge a b hb] at hcc
  rw [← R.swapBlack_face a b] at hfc
  change Nat.card (Cycles (R.swapBlack a b).black) + 1 = _ at hbc
  have hw : (R.swapBlack a b).white = R.white := rfl
  unfold Ribbon.GenusZero at hR ⊢
  rw [hw]
  omega

lemma Ribbon.genusZero_swapBlack_split (R : Ribbon α) (hR : R.GenusZero) (a b : α)
    (hne : a ≠ b) (hab : R.black.SameCycle a b) : (R.swapBlack a b).GenusZero := by
  let S := R.swapBlack a b
  have hback : S.swapBlack a b = R := R.swapBlack_twice a b
  have hn : ¬ S.black.SameCycle a b := not_sameCycle_swap_of_sameCycle R.black a b hne hab
  have hbc := swap_mul_cycles_card_split R.black a b hne hab
  change Nat.card (Cycles S.black) = Nat.card (Cycles R.black) + 1 at hbc
  have hw : S.white = R.white := rfl
  have hcomp := S.swapBlack_components_merge a b hn
  rw [hback] at hcomp
  by_cases hc : S.components.r a b
  · rw [joinPair_eq_of_related S.components hc] at hcomp
    have hfc := swap_cycles_card_le S.face (S.white a) (S.white b)
    rw [← S.swapBlack_face a b, hback] at hfc
    have hbnd := S.euler_le
    unfold Ribbon.GenusZero at hR ⊢
    change Nat.card (Cycles S.black) + Nat.card (Cycles S.white) +
      Nat.card (Cycles S.face) = Fintype.card α + 2 * Nat.card (Quotient S.components)
    rw [hw] at hbnd ⊢
    rw [hcomp] at hR
    omega
  · have hcc := joinPair_card S.components a b hc
    rw [← hcomp] at hcc
    have hfc := swap_mul_cycles_card S.face (S.white a) (S.white b)
      (S.not_white_faceCycle_of_not_component hc)
    rw [← S.swapBlack_face a b, hback] at hfc
    unfold Ribbon.GenusZero at hR ⊢
    change Nat.card (Cycles S.black) + Nat.card (Cycles S.white) +
      Nat.card (Cycles S.face) = Fintype.card α + 2 * Nat.card (Quotient S.components)
    rw [hw]
    omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse14} {V : Type portUniverse15} {F : Type portUniverse16} {A : Type portUniverse17} {B : Type portUniverse18} [sectionInstance2 : Fintype α] [CommGroup A] [Group B]

structure NoncommBalanced (R : Ribbon α) (Inc : V → F → Prop)
    (ι : V → F → (A →* B)) where
  blackLabel : α → V
  whiteLabel : α → F
  blackLabel_rot : ∀ a, blackLabel (R.black a) = blackLabel a
  whiteLabel_rot : ∀ a, whiteLabel (R.white a) = whiteLabel a
  incident : ∀ a, Inc (blackLabel a) (whiteLabel a)
  weight : α → A
  white_prod : ∀ c : Cycles R.white, ∏ a ∈ cycleSet R.white c, weight a = 1
  potential : α → B
  exception : α
  black_balance : ∀ a, a ≠ exception →
    potential (R.black a) = potential a * ι (blackLabel a) (whiteLabel a) (weight a)
  black_defect : potential (R.black exception) ≠ potential exception *
    ι (blackLabel exception) (whiteLabel exception) (weight exception)

def NoncommBalanced.Reduced {R : Ribbon α} {Inc : V → F → Prop}
    {ι : V → F → (A →* B)} (D : NoncommBalanced R Inc ι) : Prop :=
  (∀ a, D.weight a ≠ 1) ∧
  (∀ a, R.black a ≠ a → D.whiteLabel (R.black a) ≠ D.whiteLabel a) ∧
  (∀ a, R.white a ≠ a → D.blackLabel (R.white a) ≠ D.blackLabel a)

lemma cycleSet_singleton_of_fixed (p : Perm α) (a : α) (h : p a = a) :
    cycleSet p (cycleClass p a) = {a} := by
  classical
  ext b
  rw [mem_cycleSet, cycleClass_eq, Finset.mem_singleton]
  exact ⟨fun hb => hb.eq_of_right h, fun hb => hb ▸ SameCycle.refl p a⟩

lemma cycleSet_card_pow (p : Perm α) (a : α) :
    (p ^ (cycleSet p (cycleClass p a)).card) a = a := by
  classical
  by_cases h : p a = a
  · rw [cycleSet_singleton_of_fixed p a h, Finset.card_singleton, pow_one, h]
  · have heq : cycleSet p (cycleClass p a) = (p.cycleOf a).support := by
      ext b
      rw [mem_cycleSet, cycleClass_eq, mem_support_cycleOf_iff' h, sameCycle_comm]
    rw [heq, ← p.pow_mod_card_support_cycleOf_self_apply]
    simp only [Nat.mod_self, pow_zero, coe_one, id_eq]

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →* B)}

lemma NoncommBalanced.white_not_fixed (D : NoncommBalanced R Inc ι)
    (hw : ∀ a, D.weight a ≠ 1) (a : α) : R.white a ≠ a := by
  intro h
  have hp := D.white_prod (cycleClass R.white a)
  rw [cycleSet_singleton_of_fixed R.white a h, Finset.prod_singleton] at hp
  exact hw a hp

lemma NoncommBalanced.black_iterate (D : NoncommBalanced R Inc ι)
    (a : α) (ha : ¬ R.black.SameCycle a D.exception) (n : ℕ) :
    D.potential ((R.black^n) a) = D.potential a *
      ((List.range n).map fun k =>
        ι (D.blackLabel ((R.black^k) a)) (D.whiteLabel ((R.black^k) a))
          (D.weight ((R.black^k) a))).prod := by
  induction n with
  | zero => simp only [pow_zero, coe_one, id_eq, List.range_zero, List.map_nil, List.prod_nil, mul_one]
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, D.black_balance, ih, List.range_succ,
      List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, mul_assoc]
    intro he
    apply ha
    rw [← he]
    exact (SameCycle.refl R.black a).pow_right (n := n)

end OddKaplansky.Planar

namespace OddKaplansky.Holonomy
open Equiv Equiv.Perm
variable {α : Type portUniverse19} {B : Type portUniverse20} [Group B]

structure Defect (p : Perm α) (w : α → B) where
  potential : α → B
  exception : α
  balance : ∀ x, x ≠ exception → potential (p x) = potential x * w x
  defective : potential (p exception) ≠ potential exception * w exception

noncomputable def combineWeight (w : α → B) (a b x : α) : B :=
  if x = a then 1 else if x = b then w a * w b else w x
noncomputable def combinePotential (t : α → B) (a b x : α) : B :=
  if x = b then t a else t x

def Defect.combine {p : Perm α} {w : α → B} (D : Defect p w)
    (a b : α) (hab : a ≠ b) (hpa : p a = b) :
    Defect p (combineWeight w a b) := by
  classical
  let t := combinePotential D.potential a b
  have hpb : p b ≠ b := by
    intro h
    exact hab (p.injective (hpa.trans h.symm))
  have ht (x : α) (hx : x ≠ b) : t x = D.potential x :=
    if_neg hx
  have hta : t a = D.potential a := ht a hab
  have htb : t b = D.potential a := if_pos rfl
  have hxa (x : α) (hx : x ≠ a) : p x ≠ b := by
    intro h
    exact hx (p.injective (h.trans hpa.symm))
  have hbalance_a : t (p a) = t a * combineWeight w a b a := by
    rw [hpa, htb, hta]
    simp only [combineWeight, ↓reduceIte, mul_one]
  have hbalance_b (ha : a ≠ D.exception) (hb : b ≠ D.exception) :
      t (p b) = t b * combineWeight w a b b := by
    rw [ht _ hpb, htb, D.balance b hb, ← hpa, D.balance a ha, hpa]
    simp only [mul_assoc, combineWeight, hab.symm, ↓reduceIte]
  have hbalance_other (x : α) (hxa' : x ≠ a) (hxb : x ≠ b)
      (hxe : x ≠ D.exception) : t (p x) = t x * combineWeight w a b x := by
    rw [ht _ (hxa x hxa'), ht _ hxb, D.balance x hxe]
    simp only [combineWeight, hxa', ↓reduceIte, hxb]
  by_cases hea : D.exception = a
  · refine ⟨t, b, ?_, ?_⟩
    · intro x hxb
      by_cases hxa' : x = a
      · subst x; exact hbalance_a
      · exact hbalance_other x hxa' hxb (by simpa only [hea, ne_eq] using hxa')
    · intro h
      have he := D.defective
      rw [hea, hpa] at he
      apply he
      rw [ht _ hpb, htb, D.balance b (by simpa only [hea, ne_eq] using hab.symm)] at h
      simp only [combineWeight, hab.symm, ↓reduceIte, ← mul_assoc, mul_left_inj] at h
      exact h
  · refine ⟨t, D.exception, ?_, ?_⟩
    · intro x hxe
      by_cases hxa' : x = a
      · subst x; exact hbalance_a
      · by_cases hxb : x = b
        · subst x; exact hbalance_b (Ne.symm hea) hxe
        · exact hbalance_other x hxa' hxb hxe
    · intro h
      apply D.defective
      by_cases heb : D.exception = b
      · rw [heb, ht _ hpb, htb, show combineWeight w a b b = w a * w b by
          simp only [combineWeight, hab.symm, ↓reduceIte]] at h
        rw [heb]
        have htba := D.balance a (Ne.symm hea)
        rw [hpa] at htba
        rw [htba, mul_assoc]
        exact h
      · rw [ht _ (hxa _ hea), ht _ heb] at h
        simpa only [combineWeight, hea, ↓reduceIte, heb] using h

def Defect.merge {p : Perm α} {w : α → B} (D : Defect p w)
    (a b : α) (hab : ¬ p.SameCycle a b) : Defect (swap a b * p) w := by
  classical
  let u : B := D.potential a * (D.potential b)⁻¹
  let k (x : α) : B := if p.SameCycle b x then u else 1
  let t (x : α) : B := k x * D.potential x
  have hba : ¬ p.SameCycle b a := fun h => hab h.symm
  have hka : k a = 1 := if_neg hba
  have hkb : k b = u := if_pos (SameCycle.refl p b)
  have hkp (x : α) : k (p x) = k x := by simp only [k, sameCycle_apply_right]
  have htarget (x : α) : t ((swap a b * p) x) = k x * D.potential (p x) := by
    by_cases hxa : p x = a
    · have hkx : k x = 1 := by rw [← hkp, hxa, hka]
      simp only [Perm.mul_apply, hxa, swap_apply_left, hkb, inv_mul_cancel_right, hkx, one_mul, t, u]
    · by_cases hxb : p x = b
      · have hkx : k x = u := by rw [← hkp, hxb, hkb]
        simp only [Perm.mul_apply, hxb, swap_apply_right, hka, one_mul, hkx, inv_mul_cancel_right, t, u]
      · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxa hxb]
        change k (p x) * D.potential (p x) = _
        rw [hkp]
  refine ⟨t, D.exception, ?_, ?_⟩
  · intro x hx
    rw [htarget, D.balance x hx, ← mul_assoc]
  · intro h
    apply D.defective
    rw [htarget] at h
    change k D.exception * D.potential (p D.exception) =
      k D.exception * D.potential D.exception * w D.exception at h
    rw [mul_assoc] at h
    exact mul_left_cancel h

def Defect.swapEqual {p : Perm α} {w : α → B} (D : Defect p w)
    (a b : α) (hab : D.potential a = D.potential b) :
    Defect (swap a b * p) w := by
  classical
  have ht (x : α) : D.potential ((swap a b * p) x) = D.potential (p x) := by
    apply OddKaplansky.Planar.label_swap
    exact hab
  refine ⟨D.potential, D.exception, ?_, ?_⟩
  · intro x hx
    rw [ht]
    exact D.balance x hx
  · rw [ht]
    exact D.defective

def Defect.splitRestrict {p : Perm α} {w : α → B} (D : Defect p w)
    (a b : α) (hab : D.potential a ≠ D.potential b)
    (P : α → Prop) (hP : ∀ x, P ((swap a b * p) x) ↔ P x)
    (ha : P a) (hb : ¬ P b) (he : ¬ P D.exception) :
    Defect ((swap a b * p).subtypePerm hP) (fun x => w x.val) := by
  classical
  have hab' : a ≠ b := fun h => hab (congrArg D.potential h)
  have hq : (swap a b * p) (p.symm b) = a := by simp only [coe_mul, Function.comp_apply, apply_symm_apply, swap_apply_right]
  have hd : P (p.symm b) := (hP _).mp (by rw [hq]; exact ha)
  refine ⟨(fun x => D.potential x.val), ⟨p.symm b, hd⟩, ?_, ?_⟩
  · intro x hx
    have hxe : x.val ≠ D.exception := fun h => he (h ▸ x.prop)
    have hxb : p x.val ≠ b := by
      intro h
      apply hx
      apply Subtype.ext
      exact p.injective (h.trans (p.apply_symm_apply b).symm)
    have hxa : p x.val ≠ a := by
      intro h
      have hqx : (swap a b * p) x.val = b := by simp only [Perm.mul_apply, h, swap_apply_left]
      exact hb (hqx ▸ (hP x).mpr x.prop)
    change D.potential ((swap a b * p) x.val) = D.potential x.val * w x.val
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxa hxb]
    exact D.balance x hxe
  · change D.potential ((swap a b * p) (p.symm b)) ≠
      D.potential (p.symm b) * w (p.symm b)
    rw [hq, ← D.balance (p.symm b) (fun h => he (h ▸ hd)), p.apply_symm_apply]
    exact hab

def Defect.unplug {p : Perm α} {w : α → B} (D : Defect p w)
    (a : α) (hwa : w a = 1) : Defect (OddKaplansky.Planar.unplug p a) w := by
  classical
  by_cases hpa : p a = a
  · have hq : OddKaplansky.Planar.unplug p a = p := by
      ext x
      simp only [Planar.unplug, hpa, swap_self, coe_mul, coe_refl, Function.comp_apply, id_eq]
    rw [hq]
    exact D
  let b := p.symm a
  have hpb : p b = a := p.apply_symm_apply a
  have hba : b ≠ a := by
    intro h
    apply hpa
    rwa [h] at hpb
  let q := OddKaplansky.Planar.unplug p a
  have hqa : q a = a := OddKaplansky.Planar.unplug_fixed p a
  have hqb : q b = p a := by simp only [Planar.unplug, coe_mul, Function.comp_apply, hpb, swap_apply_left, q]
  have hqx (x : α) (hxa : x ≠ a) (hxb : x ≠ b) : q x = p x := by
    have hpxa : p x ≠ a := fun h => hxb (p.injective (h.trans hpb.symm))
    have hpxpa : p x ≠ p a := fun h => hxa (p.injective h)
    exact swap_apply_of_ne_of_ne hpxa hpxpa
  have hbalance_a : D.potential (q a) = D.potential a * w a := by rw [hqa, hwa, mul_one]
  by_cases hea : D.exception = a
  · refine ⟨D.potential, b, ?_, ?_⟩
    · intro x hxb
      by_cases hxa : x = a
      · subst x; exact hbalance_a
      · rw [hqx x hxa hxb]
        exact D.balance x (by simpa only [hea, ne_eq] using hxa)
    · intro h
      apply D.defective
      have hh := D.balance b (by simpa only [hea, ne_eq] using hba)
      rw [hpb] at hh
      change D.potential (q b) = D.potential b * w b at h
      rw [hqb, ← hh] at h
      simpa only [hea, hwa, mul_one] using h
  · have ha : D.potential (p a) = D.potential a := by
      simpa only [hwa, mul_one] using D.balance a (Ne.symm hea)
    refine ⟨D.potential, D.exception, ?_, ?_⟩
    · intro x hxe
      by_cases hxa : x = a
      · subst x; exact hbalance_a
      · by_cases hxb : x = b
        · subst x
          rw [hqb, ha, ← hpb]
          exact D.balance b hxe
        · rw [hqx x hxa hxb]
          exact D.balance x hxe
    · intro h
      apply D.defective
      by_cases heb : D.exception = b
      · change D.potential (q D.exception) = _ at h
        rw [heb, hqb, ha] at h
        simpa only [heb, hpb] using h
      · rw [hqx D.exception hea heb] at h
        exact h

end OddKaplansky.Holonomy

namespace OddKaplansky.Planar
open Equiv Equiv.Perm OddKaplansky.Holonomy
variable {α : Type portUniverse21} {β : Type portUniverse22} {V : Type portUniverse23} {F : Type portUniverse24} {A : Type portUniverse25} {B : Type portUniverse26} [sectionInstance3 : Fintype α] [CommGroup A] [Group B]

def cycleMap {p q : Perm α} (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y) :
    Cycles p → Cycles q := Quotient.map id (fun _ _ hxy => h hxy)

omit [Fintype α] in
lemma cycleMap_class {p q : Perm α} (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y)
    (a : α) : cycleMap h (cycleClass p a) = cycleClass q a := rfl

lemma prod_cycle_coarsen {p q : Perm α}
    (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y) (c : Cycles q) (f : α → A) :
    ∏ a ∈ cycleSet q c, f a =
      ∏ d ∈ Finset.univ.filter (fun d : Cycles p => cycleMap h d = c),
        ∏ a ∈ cycleSet p d, f a := by
  classical
  have hh := Finset.prod_fiberwise_eq_prod_filter (Finset.univ : Finset α)
    (Finset.univ.filter (fun d : Cycles p => cycleMap h d = c)) (cycleClass p) f
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, cycleMap_class, cycleSet]
    using hh.symm

lemma prod_cycle_coarsen_one {p q : Perm α}
    (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y) (f : α → A)
    (hf : ∀ c : Cycles p, ∏ a ∈ cycleSet p c, f a = 1) (c : Cycles q) :
    ∏ a ∈ cycleSet q c, f a = 1 := by
  rw [prod_cycle_coarsen h]
  simp only [hf, Finset.prod_const_one]

lemma label_sameCycle (p : Perm α) (f : α → β) (hf : ∀ a, f (p a) = f a)
    {x y : α} (hxy : p.SameCycle x y) : f x = f y :=
  setoid_sameCycle_of_step (Setoid.ker f) p (fun x => (hf x).symm) hxy

lemma label_unplug (p : Perm α) (f : α → β) (hf : ∀ a, f (p a) = f a) (a x : α) :
    f (unplug p a x) = f x :=
  (label_sameCycle p f hf (unplug_sameCycle p a ((SameCycle.refl _ x).apply_right))).symm

lemma sameCycle_unplug_iff_of_ne (p : Perm α) (a : α) {x y : α}
    (hx : x ≠ a) (hy : y ≠ a) : (unplug p a).SameCycle x y ↔ p.SameCycle x y := by
  by_cases ha : p a = a
  · simp only [unplug, ha, swap_self]
    rfl
  · exact unplug_sameCycle_iff p a ha hx hy

lemma cycleSet_unplug (p : Perm α) (a x : α) (hx : x ≠ a) :
    cycleSet (unplug p a) (cycleClass (unplug p a) x) =
      (cycleSet p (cycleClass p x)).erase a := by
  classical
  ext y
  rw [mem_cycleSet, cycleClass_eq, Finset.mem_erase, mem_cycleSet, cycleClass_eq]
  constructor
  · intro hy
    refine ⟨?_, unplug_sameCycle p a hy⟩
    intro hya
    subst y
    exact hx (hy.symm.eq_of_right (unplug_fixed p a))
  · rintro ⟨hya, hy⟩
    exact (sameCycle_unplug_iff_of_ne p a hya hx).mpr hy

omit [Fintype α] in
lemma prod_erase_of_one (s : Finset α) (a : α) (f : α → A) (ha : f a = 1) :
    ∏ x ∈ s.erase a, f x = ∏ x ∈ s, f x := by
  classical
  apply Finset.prod_subset (Finset.erase_subset _ _)
  intro x hx hxa
  have : x = a := by simpa only [Finset.mem_erase, ne_eq, hx, and_true, Decidable.not_not] using hxa
  simpa only [this] using ha

lemma prod_cycle_unplug (p : Perm α) (a x : α) (hx : x ≠ a)
    (f : α → A) (ha : f a = 1) :
    ∏ y ∈ cycleSet (unplug p a) (cycleClass (unplug p a) x), f y =
      ∏ y ∈ cycleSet p (cycleClass p x), f y := by
  rw [cycleSet_unplug p a x hx]
  exact prod_erase_of_one _ a f ha

def cycleSubtypeMap (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x) :
    Cycles (p.subtypePerm hP) → Cycles p :=
  Quotient.map Subtype.val (fun _ _ h => (sameCycle_subtypePerm (h := hP)).mp h)

lemma prod_cycle_subtype (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x)
    (c : Cycles (p.subtypePerm hP)) (f : α → A) :
    ∏ a ∈ cycleSet (p.subtypePerm hP) c, f a.val =
      ∏ a ∈ cycleSet p (cycleSubtypeMap p P hP c), f a := by
  classical
  induction c using Quotient.inductionOn with
  | h x =>
    apply Finset.prod_bij (fun y _ => y.val)
    · intro y hy
      apply (mem_cycleSet _ _ _).mpr
      exact Quotient.sound ((sameCycle_subtypePerm (h := hP)).mp
        (Quotient.exact ((mem_cycleSet _ _ _).mp hy)))
    · intro y _ z _ h
      exact Subtype.ext h
    · intro y hy
      have hcycle : p.SameCycle y x.val := (cycleClass_eq _ _ _).mp ((mem_cycleSet _ _ _).mp hy)
      have hPy : P y := (perm_invariant_cycle p P hP hcycle).mpr x.property
      refine ⟨⟨y, hPy⟩, ?_, rfl⟩
      apply (mem_cycleSet _ _ _).mpr
      exact Quotient.sound ((sameCycle_subtypePerm (h := hP)).mpr hcycle)
    · intro _ _
      rfl

lemma prod_combineWeight
    {α : Type contextUniverse1}
    {A : Type contextUniverse2}
    [Fintype.{contextUniverse1} α]
    [CommGroup.{contextUniverse2} A] (s : Finset α) (w : α → A) (a b : α) (hab : a ≠ b)
    (hmem : a ∈ s ↔ b ∈ s) : ∏ x ∈ s, combineWeight w a b x = ∏ x ∈ s, w x := by
  classical
  have heq (x : α) : combineWeight w a b x =
      w x * (if x = b then w a else 1) / (if x = a then w a else 1) := by
    by_cases hxa : x = a
    · subst x; simp only [combineWeight, ↓reduceIte, hab, mul_one, div_self']
    · by_cases hxb : x = b
      · subst x; simp only [combineWeight, hab.symm, ↓reduceIte, mul_comm, div_one]
      · simp only [combineWeight, hxa, ↓reduceIte, hxb, mul_one, div_one]
  simp only [heq, Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp only [hmem, mul_div_cancel_right]

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →* B)}

def NoncommBalanced.localWeight (D : NoncommBalanced R Inc ι) (x : α) : B :=
  ι (D.blackLabel x) (D.whiteLabel x) (D.weight x)

def NoncommBalanced.defect (D : NoncommBalanced R Inc ι) : Defect R.black D.localWeight :=
  ⟨D.potential, D.exception, D.black_balance, D.black_defect⟩

def NoncommBalanced.withDefect (D : NoncommBalanced R Inc ι) (w : α → A)
    (hw : ∀ c : Cycles R.white, ∏ x ∈ cycleSet R.white c, w x = 1)
    (E : Defect R.black (fun x => ι (D.blackLabel x) (D.whiteLabel x) (w x))) :
    NoncommBalanced R Inc ι :=
  { D with
    weight := w
    white_prod := hw
    potential := E.potential
    exception := E.exception
    black_balance := E.balance
    black_defect := E.defective }

def NoncommBalanced.combine (D : NoncommBalanced R Inc ι) (a b : α)
    (hab : a ≠ b) (hpa : R.black a = b) (hw : R.white.SameCycle a b) :
    NoncommBalanced R Inc ι := by
  have hbl : D.blackLabel b = D.blackLabel a := by rw [← hpa, D.blackLabel_rot]
  have hwl : D.whiteLabel b = D.whiteLabel a :=
    (label_sameCycle R.white D.whiteLabel D.whiteLabel_rot hw).symm
  have hm : (fun x => ι (D.blackLabel x) (D.whiteLabel x) (combineWeight D.weight a b x)) =
      combineWeight D.localWeight a b := by
    funext x
    by_cases hxa : x = a
    · subst x; simp only [combineWeight, ↓reduceIte, map_one]
    · by_cases hxb : x = b
      · subst x; simp only [hbl, hwl, combineWeight, hab.symm, ↓reduceIte, map_mul, localWeight]
      · simp only [combineWeight, hxa, ↓reduceIte, hxb, localWeight]
  refine D.withDefect (combineWeight D.weight a b) ?_ ?_
  · intro c
    rw [prod_combineWeight _ _ _ _ hab]
    · exact D.white_prod c
    · rw [mem_cycleSet, mem_cycleSet, (cycleClass_eq R.white a b).mpr hw]
  · rw [hm]
    exact D.defect.combine a b hab hpa

def NoncommBalanced.restrict (D : NoncommBalanced R Inc ι) (P : α → Prop)
    (hb : ∀ x, P (R.black x) ↔ P x) (hw : ∀ x, P (R.white x) ↔ P x)
    (he : P D.exception) : NoncommBalanced (R.restrict P hb hw) Inc ι where
  blackLabel x := D.blackLabel x.val
  whiteLabel x := D.whiteLabel x.val
  blackLabel_rot x := D.blackLabel_rot x.val
  whiteLabel_rot x := D.whiteLabel_rot x.val
  incident x := D.incident x.val
  weight x := D.weight x.val
  white_prod c := by
    dsimp only [Ribbon.restrict] at c ⊢
    rw [prod_cycle_subtype R.white P hw c D.weight]
    exact D.white_prod _
  potential x := D.potential x.val
  exception := ⟨D.exception, he⟩
  black_balance x hx := D.black_balance x.val (fun h => hx (Subtype.ext h))
  black_defect := D.black_defect

def NoncommBalanced.detach (D : NoncommBalanced R Inc ι) (a : α) (ha : D.weight a = 1) :
    NoncommBalanced (R.detach a) Inc ι := by
  let E := D.defect.unplug a (by simp only [localWeight, ha, map_one])
  refine { D with
    blackLabel_rot := label_unplug R.black D.blackLabel D.blackLabel_rot a
    whiteLabel_rot := label_unplug R.white D.whiteLabel D.whiteLabel_rot a
    potential := E.potential
    exception := E.exception
    white_prod := ?_
    black_balance := E.balance
    black_defect := E.defective }
  intro c
  induction c using Quotient.inductionOn with
  | h x =>
    change (∏ y ∈ cycleSet (unplug R.white a) (cycleClass (unplug R.white a) x), D.weight y) = 1
    by_cases hx : x = a
    · subst x
      rw [cycleSet_singleton_of_fixed _ _ (unplug_fixed R.white a), Finset.prod_singleton, ha]
    · rw [prod_cycle_unplug R.white a x hx D.weight ha]
      exact D.white_prod _

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm OddKaplansky.Holonomy
variable {α : Type u} {V : Type portUniverse27} {F : Type portUniverse28} {A : Type portUniverse29} {B : Type portUniverse30} [Fintype α] [CommGroup A] [Group B]
variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →* B)}

def NoncommBalanced.mergeWhite (D : NoncommBalanced R Inc ι) (a : α)
    (ha : ¬ R.white.SameCycle a (R.black a))
    (hl : D.whiteLabel (R.black a) = D.whiteLabel a) :
    NoncommBalanced (R.mergeWhite a) Inc ι := by
  have hn : ¬ R.white.SameCycle a (R.face a) := by simpa only [Ribbon.face, coe_mul, Function.comp_apply, sameCycle_apply_right] using ha
  have hlabel : D.whiteLabel a = D.whiteLabel (R.face a) := by
    rw [Ribbon.face, Perm.mul_apply, D.whiteLabel_rot, hl]
  refine { D with whiteLabel_rot := ?_, white_prod := ?_ }
  · intro x
    change D.whiteLabel (swap a (R.face a) (R.white x)) = D.whiteLabel x
    rw [label_swap D.whiteLabel a (R.face a) hlabel, D.whiteLabel_rot]
  · intro c
    exact prod_cycle_coarsen_one (sameCycle_swap_mul R.white a (R.face a) hn)
      D.weight D.white_prod c

def NoncommBalanced.spliceBlack (D : NoncommBalanced R Inc ι) (a b : α)
    (hl : D.blackLabel a = D.blackLabel b)
    (E : Defect (swap a b * R.black) D.localWeight) :
    NoncommBalanced (R.swapBlack a b) Inc ι := by
  refine { D with
    blackLabel_rot := ?_
    potential := E.potential
    exception := E.exception
    black_balance := E.balance
    black_defect := E.defective }
  intro x
  change D.blackLabel (swap a b (R.black x)) = D.blackLabel x
  rw [label_swap D.blackLabel a b hl, D.blackLabel_rot]

omit [Fintype α] in
lemma fixed_compl_invariant (p : Perm α) (a : α) (ha : p a = a) (x : α) :
    p x ≠ a ↔ x ≠ a := by
  constructor
  · intro h hxa; subst x; exact h ha
  · intro h hpx; exact h (p.injective (hpx.trans ha.symm))

lemma NoncommBalanced.exists_smaller (D : NoncommBalanced R Inc ι) (hR : R.GenusZero)
    (a : α) (ha : D.weight a = 1) :
    ∃ (β : Type u) (iβ : Fintype β) (S : Ribbon β),
      @Fintype.card β iβ < Fintype.card α ∧ @Ribbon.GenusZero β iβ S ∧
        Nonempty (@NoncommBalanced β V F A B iβ _ _ S Inc ι) := by
  classical
  let D' := D.detach a ha
  have hea : D'.exception ≠ a := by
    intro he
    apply D'.black_defect
    rw [he]
    change D'.potential ((R.detach a).black a) =
      D'.potential a * ι (D.blackLabel a) (D.whiteLabel a) (D.weight a)
    rw [R.detach_fixed_black a, ha, map_one, mul_one]
  let hb := fixed_compl_invariant (R.detach a).black a (R.detach_fixed_black a)
  let hw := fixed_compl_invariant (R.detach a).white a (R.detach_fixed_white a)
  let S := (R.detach a).restrict (fun x => x ≠ a) hb hw
  have hcard : Fintype.card {x : α // x ≠ a} < Fintype.card α :=
    Fintype.card_subtype_lt (x := a) (by simp only [ne_eq, not_true_eq_false, not_false_eq_true])
  refine ⟨{x : α // x ≠ a}, _, S, ?_,
    (R.detach a).planar_restrict (R.genusZero_detach hR a) (fun x : α => x ≠ a) hb hw, ?_⟩
  · convert hcard
  · exact ⟨D'.restrict (fun x => x ≠ a) hb hw hea⟩

lemma Ribbon.mergeBlack_separates (R : Ribbon α) (hR : R.GenusZero) (a : α)
    (hne : a ≠ R.black (R.white a))
    (hs : R.black.SameCycle a (R.black (R.white a))) :
    ¬ (R.mergeBlack a).components.r a (R.black (R.white a)) := by
  let b := R.black (R.white a)
  let S := R.swapBlack a b
  have hback : S.swapBlack a b = R := R.swapBlack_twice a b
  have hn : ¬ S.black.SameCycle a b := not_sameCycle_swap_of_sameCycle R.black a b hne hs
  have hbc := swap_mul_cycles_card_split R.black a b hne hs
  have hf : R.face (R.white a) ≠ R.white a := by
    intro h
    exact hne (R.white.injective h).symm
  have hfc := unplug_cycles_card R.face (R.white a) hf
  rw [← R.mergeBlack_face a] at hfc
  have hcomp := S.swapBlack_components_merge a b hn
  rw [hback] at hcomp
  intro hc
  change S.components.r a b at hc
  rw [joinPair_eq_of_related S.components hc] at hcomp
  have hbnd := S.euler_le
  change Nat.card (Cycles S.black) = Nat.card (Cycles R.black) + 1 at hbc
  change Nat.card (Cycles S.face) = Nat.card (Cycles R.face) + 1 at hfc
  have hw : S.white = R.white := rfl
  rw [hw, ← hcomp] at hbnd
  unfold Ribbon.GenusZero at hR
  omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse31} {V : Type portUniverse32} {F : Type portUniverse33} {A : Type portUniverse34} {B : Type portUniverse35} [Fintype α] [CommGroup A] [Group B]

structure ShortWords (Inc : V → F → Prop) (ι : V → F → (A →* B)) : Prop where
  one : ∀ v f, Inc v f → ∀ a, a ≠ 1 → ι v f a ≠ 1
  two : ∀ v f g, Inc v f → Inc v g → f ≠ g →
    ∀ a b, a ≠ 1 → b ≠ 1 → ι v f a * ι v g b ≠ 1
  three : ∀ v f g h, Inc v f → Inc v g → Inc v h →
    f ≠ g → g ≠ h → h ≠ f →
    ∀ a b c, a ≠ 1 → b ≠ 1 → c ≠ 1 → ι v f a * ι v g b * ι v h c ≠ 1

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →* B)}

lemma NoncommBalanced.black_fixed_exception (D : NoncommBalanced R Inc ι)
    (hred : D.Reduced) (hshort : ShortWords Inc ι) (a : α) (ha : R.black a = a) :
    a = D.exception := by
  by_contra hn
  have h := D.black_balance a hn
  rw [ha] at h
  apply hshort.one _ _ (D.incident a) _ (hred.1 a)
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

lemma NoncommBalanced.cycle_product_eq_one (D : NoncommBalanced R Inc ι)
    (a : α) (ha : ¬ R.black.SameCycle a D.exception) (n : ℕ)
    (hn : (R.black^n) a = a) :
    ((List.range n).map fun k =>
      ι (D.blackLabel ((R.black^k) a)) (D.whiteLabel ((R.black^k) a))
        (D.weight ((R.black^k) a))).prod = 1 := by
  have h := D.black_iterate a ha n
  rw [hn] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

lemma NoncommBalanced.black_degree (D : NoncommBalanced R Inc ι) (hred : D.Reduced)
    (hshort : ShortWords Inc ι) (c : Cycles R.black) :
    4 ≤ (cycleSet R.black c).card + if c = cycleClass R.black D.exception then 3 else 0 := by
  classical
  have hpos := (cycleSet_nonempty R.black c).card_pos
  by_cases hc : c = cycleClass R.black D.exception
  · rw [if_pos hc]; omega
  rw [if_neg hc, add_zero]
  obtain ⟨a, ha⟩ := cycleSet_nonempty R.black c
  have hac : cycleClass R.black a = c := (mem_cycleSet _ _ _).mp ha
  have hae : ¬ R.black.SameCycle a D.exception := by
    intro h
    exact hc (hac.symm.trans ((cycleClass_eq _ _ _).mpr h))
  have hb : D.blackLabel (R.black a) = D.blackLabel a := D.blackLabel_rot a
  have hbb : D.blackLabel ((R.black^2) a) = D.blackLabel a := by
    simp only [pow_two, Perm.mul_apply, D.blackLabel_rot]
  have hp (n : ℕ) (hn : (cycleSet R.black c).card = n) : (R.black^n) a = a := by
    rw [← hn, ← hac]
    exact cycleSet_card_pow R.black a
  have hnf (hcard : 1 < (cycleSet R.black c).card) : R.black a ≠ a := by
    intro h
    rw [← hac, cycleSet_singleton_of_fixed R.black a h, Finset.card_singleton] at hcard
    omega
  by_contra! hcard
  have hs : (cycleSet R.black c).card = 1 ∨ (cycleSet R.black c).card = 2 ∨
      (cycleSet R.black c).card = 3 := by omega
  rcases hs with h1 | h2 | h3
  · have hz := D.cycle_product_eq_one a hae 1 (hp 1 h1)
    simp only [List.range_one, List.map_cons, pow_zero, coe_one, id_eq, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hz
    exact hshort.one _ _ (D.incident a) _ (hred.1 a) hz
  · have hz := D.cycle_product_eq_one a hae 2 (hp 2 h2)
    simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons, pow_zero, coe_one, id_eq, pow_one, hb, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hz
    have hi : Inc (D.blackLabel a) (D.whiteLabel (R.black a)) := by
      rw [← hb]; exact D.incident _
    exact hshort.two _ _ _ (D.incident a) hi
      (hred.2.1 a (hnf (by omega))).symm _ _ (hred.1 a) (hred.1 _) hz
  · have hz := D.cycle_product_eq_one a hae 3 (hp 3 h3)
    simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons, pow_zero, coe_one, id_eq, pow_one, hb, hbb, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hz
    have hi : Inc (D.blackLabel a) (D.whiteLabel (R.black a)) := by
      rw [← hb]; exact D.incident _
    have hj : Inc (D.blackLabel a) (D.whiteLabel ((R.black^2) a)) := by
      rw [← hbb]; exact D.incident _
    have hnf₀ := hnf (by omega)
    have hnf₁ : R.black (R.black a) ≠ R.black a := fun h => hnf₀ (R.black.injective h)
    have hnf₂ : R.black ((R.black^2) a) ≠ (R.black^2) a := by
      intro h
      exact hnf₀ (((SameCycle.refl R.black a).pow_right (n := 2)).apply_eq_self_iff.mpr h)
    have h01 := (hred.2.1 a hnf₀).symm
    have h12 : D.whiteLabel (R.black a) ≠ D.whiteLabel ((R.black^2) a) := by
      simpa only [pow_two, Perm.mul_apply] using (hred.2.1 (R.black a) hnf₁).symm
    have h20 : D.whiteLabel ((R.black^2) a) ≠ D.whiteLabel a := by
      have hh := (hred.2.1 ((R.black^2) a) hnf₂).symm
      have hh' : R.black ((R.black^2) a) = a := by
        simpa only [show 3 = 2+1 from rfl, pow_succ', Perm.mul_apply] using hp 3 h3
      rwa [hh'] at hh
    apply hshort.three _ _ _ _ (D.incident a) hi hj h01 h12 h20 _ _ _
      (hred.1 a) (hred.1 _) (hred.1 _)
    simpa only [mul_assoc] using hz

lemma NoncommBalanced.white_degree (D : NoncommBalanced R Inc ι) (hred : D.Reduced)
    (c : Cycles R.white) : 2 ≤ (cycleSet R.white c).card := by
  have hpos := (cycleSet_nonempty R.white c).card_pos
  by_contra! h
  have hc : (cycleSet R.white c).card = 1 := by omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  have hz := D.white_prod c
  rw [ha, Finset.prod_singleton] at hz
  exact hred.1 a hz

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse36} {V : Type portUniverse37} {F : Type portUniverse38} {A : Type portUniverse39} {B : Type portUniverse40} [Fintype α] [CommGroup A] [Group B]

def incidenceGraph (Inc : V → F → Prop) : SimpleGraph (Sum V F) where
  Adj x y := match x, y with
    | .inl v, .inr f => Inc v f
    | .inr f, .inl v => Inc v f
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp only [imp_self]⟩
  loopless := ⟨by intro x; cases x <;> simp only [not_false_eq_true]⟩

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →* B)}

def NoncommBalanced.exceptionFace (D : NoncommBalanced R Inc ι) : Cycles R.face :=
  cycleClass R.face D.exception

lemma NoncommBalanced.black_not_fixed_on_other_face (D : NoncommBalanced R Inc ι)
    (hred : D.Reduced) (hshort : ShortWords Inc ι) {a : α}
    (ha : cycleClass R.face a ≠ D.exceptionFace) : R.black a ≠ a := by
  intro h
  apply ha
  rw [D.black_fixed_exception hred hshort a h]
  rfl

def NoncommBalanced.halfStep (D : NoncommBalanced R Inc ι) (a : α) :
    (incidenceGraph Inc).Walk (.inr (D.whiteLabel a)) (.inr (D.whiteLabel (R.face a))) :=
  .cons (v := .inl (D.blackLabel a)) (by exact D.incident a) (.cons (by
    change Inc (D.blackLabel a) (D.whiteLabel (R.white (R.black a)))
    rw [D.whiteLabel_rot, ← D.blackLabel_rot a]
    exact D.incident (R.black a)) .nil)

lemma NoncommBalanced.halfStep_length (D : NoncommBalanced R Inc ι) (a : α) :
    (D.halfStep a).length = 2 := rfl

def NoncommBalanced.boundary (D : NoncommBalanced R Inc ι) (a : α) : (n : ℕ) →
    (incidenceGraph Inc).Walk (.inr (D.whiteLabel a))
      (.inr (D.whiteLabel ((R.face ^ n) a)))
  | 0 => .nil
  | n + 1 => (D.halfStep a).append ((D.boundary (R.face a) n).copy rfl (by
      simp only [pow_succ, Perm.mul_apply]))

lemma NoncommBalanced.boundary_length (D : NoncommBalanced R Inc ι) (a : α) (n : ℕ) :
    (D.boundary a n).length = 2 * n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [NoncommBalanced.boundary, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_copy, NoncommBalanced.halfStep_length, ih]
    omega

lemma NoncommBalanced.boundary_getVert_even (D : NoncommBalanced R Inc ι) (n k : ℕ) (hk : k ≤ n)
    (a : α) : (D.boundary a n).getVert (2 * k) =
      .inr (D.whiteLabel ((R.face ^ k) a)) := by
  induction n generalizing a k with
  | zero => have : k = 0 := Nat.le_zero.mp hk
            subst k
            rfl
  | succ n ih =>
    cases k with
    | zero => simp only [mul_zero, SimpleGraph.Walk.getVert_zero, pow_zero, coe_one, id_eq]
    | succ k =>
      simp only [NoncommBalanced.boundary, SimpleGraph.Walk.getVert_append]
      rw [if_neg (by simp only [NoncommBalanced.halfStep_length]; omega),
        SimpleGraph.Walk.getVert_copy, NoncommBalanced.halfStep_length]
      have heq : 2 * (k + 1) - 2 = 2 * k := by omega
      rw [heq, ih k (by omega)]
      simp only [pow_succ, Perm.mul_apply]

lemma NoncommBalanced.boundary_getVert_odd (D : NoncommBalanced R Inc ι) (n k : ℕ) (hk : k < n)
    (a : α) : (D.boundary a n).getVert (2 * k + 1) =
      .inl (D.blackLabel ((R.face ^ k) a)) := by
  induction n generalizing a k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [NoncommBalanced.boundary, SimpleGraph.Walk.getVert_append]
      rw [if_neg (by simp only [NoncommBalanced.halfStep_length]; omega),
        SimpleGraph.Walk.getVert_copy, NoncommBalanced.halfStep_length]
      have heq : 2 * (k + 1) + 1 - 2 = 2 * k + 1 := by omega
      rw [heq, ih k (by omega)]
      simp only [pow_succ, Perm.mul_apply]

omit [Fintype α] in
lemma cycleClass_pow (p : Perm α) (a : α) (n : ℕ) :
    cycleClass p ((p ^ n) a) = cycleClass p a :=
  (cycleClass_eq _ _ _).mpr ((SameCycle.refl p a).pow_left)

lemma NoncommBalanced.boundary_reduced (D : NoncommBalanced R Inc ι) (hred : D.Reduced)
    (hshort : ShortWords Inc ι) {a : α}
    (ha : cycleClass R.face a ≠ D.exceptionFace) (n : ℕ) :
    _root_.OAI.SimpleGraph.Walk.Reduced (D.boundary a n) := by
  apply SimpleGraph.Walk.reduced_of_getVert
  intro i hi
  rw [D.boundary_length] at hi
  have he : i = 2 * (i / 2) ∨ i = 2 * (i / 2) + 1 := by omega
  rcases he with he | he
  · rw [he, D.boundary_getVert_even n (i / 2) (by omega)]
    have hk : 2 * (i / 2) + 2 = 2 * (i / 2 + 1) := by omega
    rw [hk, D.boundary_getVert_even n (i / 2 + 1) (by omega)]
    intro h
    have hh := Sum.inr.inj h
    rw [pow_succ', Perm.mul_apply] at hh
    change D.whiteLabel ((R.face ^ (i / 2)) a) =
      D.whiteLabel (R.white (R.black ((R.face ^ (i / 2)) a))) at hh
    rw [D.whiteLabel_rot] at hh
    exact hred.2.1 _ (D.black_not_fixed_on_other_face hred hshort (by rwa [cycleClass_pow])) hh.symm
  · rw [he, D.boundary_getVert_odd n (i / 2) (by omega)]
    have hk : 2 * (i / 2) + 1 + 2 = 2 * (i / 2 + 1) + 1 := by omega
    rw [hk, D.boundary_getVert_odd n (i / 2 + 1) (by omega)]
    intro h
    have hh := Sum.inl.inj h
    rw [pow_succ', Perm.mul_apply] at hh
    change D.blackLabel ((R.face ^ (i / 2)) a) =
      D.blackLabel (R.white (R.black ((R.face ^ (i / 2)) a))) at hh
    have hn : R.white (R.black ((R.face ^ (i / 2)) a)) ≠
        R.black ((R.face ^ (i / 2)) a) :=
      D.white_not_fixed hred.1 _
    exact hred.2.2 _ hn (hh.symm.trans (D.blackLabel_rot _).symm)

lemma NoncommBalanced.face_degree (D : NoncommBalanced R Inc ι) (hred : D.Reduced)
    (hshort : ShortWords Inc ι)
    (hgirth : 8 ≤ (incidenceGraph Inc).egirth) (c : Cycles R.face) :
    4 ≤ (cycleSet R.face c).card + if c = D.exceptionFace then 4 else 0 := by
  classical
  by_cases hc : c = D.exceptionFace
  · rw [if_pos hc]; omega
  rw [if_neg hc, add_zero]
  obtain ⟨a, ha⟩ := cycleSet_nonempty R.face c
  have hac : cycleClass R.face a = c := (mem_cycleSet _ _ _).mp ha
  let n := (cycleSet R.face c).card
  have hpa : (R.face ^ n) a = a := by
    change (R.face ^ (cycleSet R.face c).card) a = a
    rw [← hac]
    exact cycleSet_card_pow R.face a
  let p : (incidenceGraph Inc).Walk (.inr (D.whiteLabel a)) (.inr (D.whiteLabel a)) :=
    (D.boundary a n).copy rfl (by rw [hpa])
  have hp : _root_.OAI.SimpleGraph.Walk.Reduced p := by
    exact (D.boundary_reduced hred hshort (by rwa [hac]) n).copy _ _
  have hlen : p.length = 2 * n := by simp only [p, SimpleGraph.Walk.length_copy,
    D.boundary_length]
  have hne : ¬ p.Nil := by
    intro h
    have := SimpleGraph.Walk.Nil.length_eq_zero h
    have hn : 0 < n := (cycleSet_nonempty R.face c).card_pos
    omega
  have hg := hgirth.trans (hp.egirth_le hne)
  rw [hlen] at hg
  have hnat : 8 ≤ 2 * n := by exact_mod_cast hg
  change 4 ≤ n
  omega

theorem NoncommBalanced.reduced_not_genusZero (D : NoncommBalanced R Inc ι)
    (hred : D.Reduced) (hshort : ShortWords Inc ι)
    (hgirth : 8 ≤ (incidenceGraph Inc).egirth) : ¬ R.GenusZero := by
  classical
  intro hR
  have hb := D.black_degree hred hshort
  have hw := D.white_degree hred
  have hf := D.face_degree hred hshort hgirth
  have hb' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.black))) => hb c)
  have hw' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.white))) => hw c)
  have hf' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.face))) => hf c)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, cycles_sum_card] at hw'
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.sum_add_distrib,
    cycles_sum_card, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hb' hf'
  have hc : 0 < Nat.card (Quotient R.components) := by
    have : Nonempty (Quotient R.components) := ⟨Quotient.mk _ D.exception⟩
    exact Nat.card_pos
  unfold Ribbon.GenusZero at hR
  simp only [Nat.card_eq_fintype_card] at hR hc
  omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm OddKaplansky.Holonomy
variable {α : Type u} {V : Type portUniverse41} {F : Type portUniverse42} {A : Type portUniverse43} {B : Type portUniverse44} [Fintype α] [CommGroup A] [Group B]
variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →* B)}

def NoncommBalanced.spliceRestrict (D : NoncommBalanced R Inc ι) (a b : α)
    (hl : D.blackLabel a = D.blackLabel b) (P : α → Prop)
    (hb : ∀ x, P ((R.swapBlack a b).black x) ↔ P x)
    (hw : ∀ x, P (R.white x) ↔ P x)
    (E : Defect ((R.swapBlack a b).black.subtypePerm hb) (fun x => D.localWeight x.val)) :
    NoncommBalanced ((R.swapBlack a b).restrict P hb hw) Inc ι where
  blackLabel x := D.blackLabel x.val
  whiteLabel x := D.whiteLabel x.val
  blackLabel_rot x := by
    change D.blackLabel (swap a b (R.black x.val)) = D.blackLabel x.val
    rw [label_swap D.blackLabel a b hl, D.blackLabel_rot]
  whiteLabel_rot x := D.whiteLabel_rot x.val
  incident x := D.incident x.val
  weight x := D.weight x.val
  white_prod c := by
    dsimp only [Ribbon.restrict, Ribbon.swapBlack] at c ⊢
    rw [prod_cycle_subtype R.white P hw c D.weight]
    exact D.white_prod _
  potential := E.potential
  exception := E.exception
  black_balance := E.balance
  black_defect := E.defective

lemma NoncommBalanced.exists_smaller_of_split (D : NoncommBalanced R Inc ι) (a b : α)
    (hl : D.blackLabel a = D.blackLabel b)
    (hS : (R.swapBlack a b).GenusZero)
    (hsep : ¬ (R.swapBlack a b).components.r a b)
    (hne : D.potential a ≠ D.potential b) :
    ∃ (β : Type u) (iβ : Fintype β) (S : Ribbon β),
      @Fintype.card β iβ < Fintype.card α ∧ @Ribbon.GenusZero β iβ S ∧
        Nonempty (@NoncommBalanced β V F A B iβ _ _ S Inc ι) := by
  classical
  have side (a b : α) (hl : D.blackLabel a = D.blackLabel b)
      (hS : (R.swapBlack a b).GenusZero)
      (hab : ¬ (R.swapBlack a b).components.r b a)
      (he : ¬ (R.swapBlack a b).components.r D.exception a)
      (hne : D.potential a ≠ D.potential b) :
      ∃ (β : Type u) (iβ : Fintype β) (S : Ribbon β),
        @Fintype.card β iβ < Fintype.card α ∧ @Ribbon.GenusZero β iβ S ∧
          Nonempty (@NoncommBalanced β V F A B iβ _ _ S Inc ι) := by
    let S := R.swapBlack a b
    let P := fun x => S.components.r x a
    let hb := S.black_component_invariant a
    let hw := S.white_component_invariant a
    let E := D.defect.splitRestrict a b hne P hb (S.components.iseqv.refl a) hab he
    refine ⟨{x // P x}, _, S.restrict P hb hw, ?_, S.planar_restrict hS P hb hw, ?_⟩
    · exact Fintype.card_subtype_lt (x := b) hab
    · exact ⟨D.spliceRestrict a b hl P hb hw E⟩
  have hswap : R.swapBlack b a = R.swapBlack a b := by
    simp only [Ribbon.swapBlack, swap_comm]
  by_cases he : (R.swapBlack a b).components.r D.exception a
  · apply side b a hl.symm
    · rwa [hswap]
    · rwa [hswap]
    · intro hb
      have hb' : (R.swapBlack a b).components.r D.exception b := by
        rwa [hswap] at hb
      exact hsep ((R.swapBlack a b).components.iseqv.trans
        ((R.swapBlack a b).components.iseqv.symm he) hb')
    · exact Ne.symm hne
  · exact side a b hl hS (fun h => hsep ((R.swapBlack a b).components.iseqv.symm h)) he hne

def NoncommBalanced.Minimal (_D : NoncommBalanced R Inc ι) : Prop :=
  ∀ (β : Type u) (iβ : Fintype β) (S : Ribbon β), @Ribbon.GenusZero β iβ S →
    Nonempty (@NoncommBalanced β V F A B iβ _ _ S Inc ι) →
    Fintype.card α ≤ @Fintype.card β iβ

lemma NoncommBalanced.minimal_no_one (D : NoncommBalanced R Inc ι) (hR : R.GenusZero)
    (hm : D.Minimal) (a : α) : D.weight a ≠ 1 := by
  intro ha
  obtain ⟨β, iβ, S, hc, hS, hD⟩ := D.exists_smaller hR a ha
  exact (not_lt_of_ge (hm β iβ S hS hD)) hc

lemma NoncommBalanced.minimal_black_reduced (D : NoncommBalanced R Inc ι)
    (hR : R.GenusZero) (hm : D.Minimal) (a : α) (ha : R.black a ≠ a) :
    D.whiteLabel (R.black a) ≠ D.whiteLabel a := by
  intro hl
  by_cases hw : R.white.SameCycle a (R.black a)
  · let E := D.combine a (R.black a) ha.symm rfl hw
    have hEm : E.Minimal := hm
    exact E.minimal_no_one hR hEm a (by simp only [combine, withDefect, combineWeight, ↓reduceIte, E])
  · let E := D.mergeWhite a hw hl
    have hER := R.genusZero_mergeWhite hR a hw
    have hab : (R.mergeWhite a).white.SameCycle a (R.black a) := by
      have h := swap_mul_sameCycle R.white a (R.face a) (by simpa only [Ribbon.face, coe_mul, Function.comp_apply, sameCycle_apply_right] using hw)
      exact h.trans ((sameCycle_swap_mul R.white a (R.face a)
        (by simpa only [Ribbon.face, coe_mul, Function.comp_apply, sameCycle_apply_right] using hw)) ((SameCycle.refl R.white (R.black a)).apply_left))
    let E' := E.combine a (R.black a) ha.symm rfl hab
    have hEm : E'.Minimal := hm
    exact E'.minimal_no_one hER hEm a (by simp only [combine, withDefect, combineWeight, ↓reduceIte, E'])

lemma NoncommBalanced.minimal_white_reduced (D : NoncommBalanced R Inc ι)
    (hR : R.GenusZero) (hm : D.Minimal) (a : α) (ha : R.white a ≠ a) :
    D.blackLabel (R.white a) ≠ D.blackLabel a := by
  classical
  intro hl
  let b := R.white a
  have hba : b ≠ a := ha
  have hw : R.white.SameCycle b a := (SameCycle.refl R.white a).apply_left
  by_cases hp : R.black b = a
  · let E := D.combine b a hba hp hw
    have hEm : E.Minimal := hm
    exact E.minimal_no_one hR hEm b (by simp only [combine, withDefect, combineWeight, ↓reduceIte, E])
  have hl' : D.blackLabel a = D.blackLabel (R.black b) := by rw [D.blackLabel_rot, hl]
  have hpa : a ≠ R.black b := Ne.symm hp
  have finish (E : Holonomy.Defect (swap a (R.black b) * R.black) D.localWeight)
      (hS : (R.swapBlack a (R.black b)).GenusZero) : False := by
    let D' := D.spliceBlack a (R.black b) hl' E
    have hrot : (R.swapBlack a (R.black b)).black b = a := by simp only [Ribbon.swapBlack, coe_mul, Function.comp_apply, swap_apply_right]
    let D'' := D'.combine b a hba hrot hw
    have hDm : D''.Minimal := hm
    exact D''.minimal_no_one hS hDm b (by simp only [combine, withDefect, combineWeight, ↓reduceIte, D''])
  by_cases hs : R.black.SameCycle a (R.black b)
  · have hS := R.genusZero_swapBlack_split hR a (R.black b) hpa hs
    by_cases ht : D.potential a = D.potential (R.black b)
    · exact finish (D.defect.swapEqual a (R.black b) ht) hS
    · have hsep := R.mergeBlack_separates hR a hpa hs
      obtain ⟨β, iβ, S, hc, hS', hD⟩ := D.exists_smaller_of_split a (R.black b) hl' hS hsep ht
      exact (not_lt_of_ge (hm β iβ S hS' hD)) hc
  · have hS : (R.swapBlack a (R.black b)).GenusZero :=
      R.genusZero_mergeBlack hR a (by simpa only [sameCycle_apply_right] using hs)
    exact finish (D.defect.merge a (R.black b) hs) hS

lemma NoncommBalanced.minimal_reduced (D : NoncommBalanced R Inc ι)
    (hR : R.GenusZero) (hm : D.Minimal) : D.Reduced :=
  ⟨D.minimal_no_one hR hm, D.minimal_black_reduced hR hm, D.minimal_white_reduced hR hm⟩

theorem NoncommBalanced.not_genusZero (D : NoncommBalanced R Inc ι)
    (hshort : ShortWords Inc ι) (hgirth : 8 ≤ (incidenceGraph Inc).egirth) :
    ¬ R.GenusZero := by
  intro hR
  let P : ℕ → Prop := fun n => ∃ (β : Type u) (iβ : Fintype β) (S : Ribbon β),
    @Fintype.card β iβ = n ∧ @Ribbon.GenusZero β iβ S ∧
      Nonempty (@NoncommBalanced β V F A B iβ _ _ S Inc ι)
  have hex : ∃ n, P n := ⟨Fintype.card α, α, inferInstance, R, rfl, hR, ⟨D⟩⟩
  classical
  obtain ⟨β, iβ, S, hcard, hS, ⟨E⟩⟩ := Nat.find_spec hex
  let := iβ
  have hm : E.Minimal := by
    intro γ iγ T hT hE
    rw [hcard]
    exact Nat.find_min' hex ⟨γ, iγ, T, rfl, hT, hE⟩
  exact E.reduced_not_genusZero (E.minimal_reduced hS hm) hshort hgirth hS

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse45} {β : Type portUniverse46}

def sumSetoid (s : Setoid α) (t : Setoid β) : Setoid (α ⊕ β) :=
  Setoid.ker (Sum.map (Quotient.mk s) (Quotient.mk t))

@[simp] lemma sumSetoid_inl (s : Setoid α) (t : Setoid β) (x y : α) :
    (sumSetoid s t).r (.inl x) (.inl y) ↔ s.r x y := by
  change (Sum.inl (Quotient.mk s x) : Quotient s ⊕ Quotient t) = .inl (Quotient.mk s y) ↔ _
  simp only [Sum.inl.injEq, Quotient.eq]

@[simp] lemma sumSetoid_inr (s : Setoid α) (t : Setoid β) (x y : β) :
    (sumSetoid s t).r (.inr x) (.inr y) ↔ t.r x y := by
  change (Sum.inr (Quotient.mk t x) : Quotient s ⊕ Quotient t) = .inr (Quotient.mk t y) ↔ _
  simp only [Sum.inr.injEq, Quotient.eq]

@[simp] lemma sumSetoid_cross (s : Setoid α) (t : Setoid β) (x : α) (y : β) :
    ¬ (sumSetoid s t).r (.inl x) (.inr y) := by
  change ¬ (Sum.inl (Quotient.mk s x) : Quotient s ⊕ Quotient t) = .inr (Quotient.mk t y)
  simp only [reduceCtorEq, not_false_eq_true]

def sumSetoidEquiv (s : Setoid α) (t : Setoid β) :
    Quotient (sumSetoid s t) ≃ Quotient s ⊕ Quotient t :=
  Setoid.quotientKerEquivOfSurjective (Sum.map (Quotient.mk s) (Quotient.mk t)) (by
    rintro (x | y)
    · induction x using Quotient.inductionOn with
      | h x => exact ⟨.inl x, rfl⟩
    · induction y using Quotient.inductionOn with
      | h y => exact ⟨.inr y, rfl⟩)

lemma sumSetoid_card [Fintype α] [Fintype β] (s : Setoid α) (t : Setoid β) :
    Nat.card (Quotient (sumSetoid s t)) = Nat.card (Quotient s) + Nat.card (Quotient t) := by
  rw [Nat.card_congr (sumSetoidEquiv s t), Nat.card_sum]

lemma sumSetoid_le {s : Setoid α} {t : Setoid β} {r : Setoid (α ⊕ β)}
    (hl : ∀ x y, s.r x y → r.r (.inl x) (.inl y))
    (hr : ∀ x y, t.r x y → r.r (.inr x) (.inr y)) : sumSetoid s t ≤ r := by
  rintro (x | x) (y | y) h
  · exact hl x y ((sumSetoid_inl _ _ _ _).mp h)
  · exact False.elim (sumSetoid_cross _ _ _ _ h)
  · exact False.elim (sumSetoid_cross _ _ _ _ ((sumSetoid s t).iseqv.symm h))
  · exact hr x y ((sumSetoid_inr _ _ _ _).mp h)

variable [Fintype α] [Fintype β]

lemma sumCongr_cycles_setoid (p : Perm α) (q : Perm β) :
    SameCycle.setoid (Equiv.sumCongr p q) = sumSetoid (SameCycle.setoid p) (SameCycle.setoid q) := by
  apply le_antisymm
  · intro x y h
    apply setoid_sameCycle_of_step _ (Equiv.sumCongr p q) _ h
    rintro (z | z) <;> simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      sumSetoid_inl, sumSetoid_inr]
    · exact SameCycle.apply_right SameCycle.rfl
    · exact SameCycle.apply_right SameCycle.rfl
  · apply sumSetoid_le
    · intro x y h
      exact sameCycle_map p (Equiv.sumCongr p q) Sum.inl
        (fun z => SameCycle.apply_right SameCycle.rfl) h
    · intro x y h
      exact sameCycle_map q (Equiv.sumCongr p q) Sum.inr
        (fun z => SameCycle.apply_right SameCycle.rfl) h

lemma sumCongr_cycles_card (p : Perm α) (q : Perm β) :
    Nat.card (Cycles (Equiv.sumCongr p q)) = Nat.card (Cycles p) + Nat.card (Cycles q) := by
  rw [Cycles, sumCongr_cycles_setoid]
  exact sumSetoid_card _ _

def Ribbon.sum (R : Ribbon α) (S : Ribbon β) : Ribbon (α ⊕ β) :=
  ⟨Equiv.sumCongr R.black S.black, Equiv.sumCongr R.white S.white⟩

omit [Fintype α] [Fintype β] in
lemma Ribbon.sum_face (R : Ribbon α) (S : Ribbon β) :
    (R.sum S).face = Equiv.sumCongr R.face S.face := by
  ext x
  cases x <;> rfl

lemma Ribbon.sum_components (R : Ribbon α) (S : Ribbon β) :
    (R.sum S).components = sumSetoid R.components S.components := by
  apply le_antisymm
  · apply (R.sum S).components_le_of_steps
    · rintro (x | x)
      · exact (sumSetoid_inl _ _ _ _).mpr (R.black_step x)
      · exact (sumSetoid_inr _ _ _ _).mpr (S.black_step x)
    · rintro (x | x)
      · exact (sumSetoid_inl _ _ _ _).mpr (R.white_step x)
      · exact (sumSetoid_inr _ _ _ _).mpr (S.white_step x)
  · apply sumSetoid_le
    · have h := R.components_le_of_steps ((R.sum S).components.comap Sum.inl)
        (fun x => (R.sum S).black_step (.inl x))
        (fun x => (R.sum S).white_step (.inl x))
      exact fun x y hxy => h hxy
    · have h := S.components_le_of_steps ((R.sum S).components.comap Sum.inr)
        (fun x => (R.sum S).black_step (.inr x))
        (fun x => (R.sum S).white_step (.inr x))
      exact fun x y hxy => h hxy

lemma Ribbon.genusZero_sum (R : Ribbon α) (S : Ribbon β)
    (hR : R.GenusZero) (hS : S.GenusZero) : (R.sum S).GenusZero := by
  unfold Ribbon.GenusZero at *
  rw [R.sum_face, R.sum_components, sumSetoid_card, Fintype.card_sum]
  change Nat.card (Cycles (Equiv.sumCongr R.black S.black)) +
    Nat.card (Cycles (Equiv.sumCongr R.white S.white)) + _ = _
  rw [sumCongr_cycles_card, sumCongr_cycles_card, sumCongr_cycles_card]
  omega

omit [Fintype α] [Fintype β] in
lemma formPerm_append_nonempty [DecidableEq α] (a b : α) (l m : List α)
    (hb : b ∉ a :: l) :
    ((a :: l) ++ (b :: m)).formPerm = swap a b * (a :: l).formPerm * (b :: m).formPerm := by
  induction l generalizing a with
  | nil => simp only [List.cons_append, List.nil_append, List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
  | cons c l ih =>
    have hba : b ≠ a := fun h => hb (by simp only [h, List.mem_cons, true_or])
    have hbc : b ≠ c := fun h => hb (by simp only [h, List.mem_cons, true_or, or_true])
    have hc : b ∉ c :: l := fun h => hb (List.mem_cons_of_mem _ h)
    have hs : swap a c * swap c b = swap a b * swap a c := by
      rw [mul_swap_eq_swap_mul]
      simp only [swap_apply_right, swap_apply_of_ne_of_ne hba hbc]
    simp only [List.cons_append, List.formPerm_cons_cons]
    rw [show c :: (l ++ b :: m) = (c :: l) ++ (b :: m) from rfl, ih c hc]
    simp only [← mul_assoc, hs]

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse47} [Fintype α]

def Ribbon.wheel (p : Perm α) : Ribbon (α ⊕ α) :=
  ⟨Equiv.sumCongr p p⁻¹, Equiv.sumComm α α⟩

def sumIndex : α ⊕ α → α := Sum.elim id id

def wheelFaceIndex (p : Perm α) : α ⊕ α → α := Sum.elim id (fun x => p⁻¹ x)

omit [Fintype α] in
@[simp] lemma wheel_white_index (p : Perm α) (x : α ⊕ α) :
    sumIndex ((Ribbon.wheel p).white x) = sumIndex x := by cases x <;> rfl

omit [Fintype α] in
@[simp] lemma wheel_face_index (p : Perm α) (x : α ⊕ α) :
    wheelFaceIndex p ((Ribbon.wheel p).face x) = wheelFaceIndex p x := by
  cases x <;> simp only [wheelFaceIndex, coe_inv, Ribbon.face, Ribbon.wheel, coe_mul, sumComm_apply, Function.comp_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.swap_inl, Sum.elim_inr, symm_apply_apply, Sum.elim_inl, id_eq, Sum.map_inr, Sum.swap_inr]

lemma wheel_white_setoid (p : Perm α) :
    SameCycle.setoid (Ribbon.wheel p).white = Setoid.ker sumIndex := by
  apply le_antisymm
  · intro x y h
    apply setoid_sameCycle_of_step _ (Ribbon.wheel p).white _ h
    exact fun z => (wheel_white_index p z).symm
  · rintro (x | x) (y | y) h <;> change x = y at h <;> subst y
    · exact SameCycle.rfl
    · exact SameCycle.apply_right SameCycle.rfl
    · exact SameCycle.apply_right SameCycle.rfl
    · exact SameCycle.rfl

lemma wheel_face_setoid (p : Perm α) :
    SameCycle.setoid (Ribbon.wheel p).face = Setoid.ker (wheelFaceIndex p) := by
  apply le_antisymm
  · intro x y h
    apply setoid_sameCycle_of_step _ (Ribbon.wheel p).face _ h
    exact fun z => (wheel_face_index p z).symm
  · rintro (x | x) (y | y) h
    · change x = y at h
      subst y
      exact SameCycle.rfl
    · change x = p⁻¹ y at h
      subst x
      change (Ribbon.wheel p).face.SameCycle (.inl (p⁻¹ y)) (.inr y)
      convert (SameCycle.apply_right
        (SameCycle.rfl (f := (Ribbon.wheel p).face) (x := Sum.inl (p⁻¹ y)))) using 1
      simp only [Ribbon.face, Ribbon.wheel, coe_inv, coe_mul, sumComm_apply, Function.comp_apply, Equiv.sumCongr_apply, Sum.map_inl, apply_symm_apply, Sum.swap_inl]
    · change p⁻¹ x = y at h
      subst y
      exact SameCycle.apply_right SameCycle.rfl
    · change p⁻¹ x = p⁻¹ y at h
      have := p.symm.injective h
      subst y
      exact SameCycle.rfl

lemma wheel_component_index (p : Perm α) :
    (Ribbon.wheel p).components = Setoid.ker (cycleClass p ∘ sumIndex) := by
  let R := Ribbon.wheel p
  apply le_antisymm
  · apply R.components_le_of_steps
    · rintro (x | x)
      · exact (cycleClass_apply p x).symm
      · change cycleClass p x = cycleClass p (p⁻¹ x)
        exact (cycleClass_eq _ _ _).mpr (by simp only [coe_inv, sameCycle_symm_apply_right, SameCycle.rfl])
    · intro x
      change cycleClass p (sumIndex x) = cycleClass p (sumIndex (R.white x))
      rw [wheel_white_index]
  · intro x y h
    have hx : R.components.r x (.inl (sumIndex x)) := by
      cases x with
      | inl x => exact R.components.iseqv.refl _
      | inr x => exact R.white_step (.inr x)
    have hy : R.components.r y (.inl (sumIndex y)) := by
      cases y with
      | inl y => exact R.components.iseqv.refl _
      | inr y => exact R.white_step (.inr y)
    have hxy : p.SameCycle (sumIndex x) (sumIndex y) := (cycleClass_eq _ _ _).mp h
    have hp : R.black.SameCycle (.inl (sumIndex x)) (.inl (sumIndex y)) :=
      sameCycle_map p R.black Sum.inl (fun z => SameCycle.apply_right SameCycle.rfl) hxy
    exact R.components.iseqv.trans hx (R.components.iseqv.trans
      ((show SameCycle.setoid R.black ≤ R.components from le_sup_left) hp)
      (R.components.iseqv.symm hy))

lemma wheel_white_card (p : Perm α) :
    Nat.card (Cycles (Ribbon.wheel p).white) = Fintype.card α := by
  rw [Cycles, wheel_white_setoid]
  exact (Nat.card_congr (Setoid.quotientKerEquivOfSurjective sumIndex
    (fun x => ⟨.inl x, rfl⟩))).trans Nat.card_eq_fintype_card

lemma wheel_face_card (p : Perm α) :
    Nat.card (Cycles (Ribbon.wheel p).face) = Fintype.card α := by
  rw [Cycles, wheel_face_setoid]
  exact (Nat.card_congr (Setoid.quotientKerEquivOfSurjective (wheelFaceIndex p)
    (fun x => ⟨.inl x, rfl⟩))).trans Nat.card_eq_fintype_card

lemma wheel_component_card (p : Perm α) :
    Nat.card (Quotient (Ribbon.wheel p).components) = Nat.card (Cycles p) := by
  rw [wheel_component_index]
  apply Nat.card_congr
  apply Setoid.quotientKerEquivOfSurjective
  intro c
  induction c using Quotient.inductionOn with
  | h x => exact ⟨.inl x, rfl⟩

lemma Ribbon.genusZero_wheel (p : Perm α) : (Ribbon.wheel p).GenusZero := by
  unfold Ribbon.GenusZero
  rw [wheel_white_card, wheel_face_card, wheel_component_card, Fintype.card_sum]
  change Nat.card (Cycles (Equiv.sumCongr p p⁻¹)) + _ + _ = _
  rw [sumCongr_cycles_card, cycles_inv_card]
  omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse48} {β : Type portUniverse49} {A : Type portUniverse50} [Fintype α]

def Follows (p : Perm α) (l : List α) : Prop := ∀ x ∈ l, p x = l.formPerm x

omit [Fintype α] in
lemma Follows.invariant {p : Perm α} {l : List α} (h : Follows p l) (x : α) :
    p x ∈ l ↔ x ∈ l := by
  classical
  constructor
  · intro hx
    let y := l.formPerm⁻¹ (p x)
    have hy : y ∈ l := by
      apply l.mem_of_formPerm_apply_mem
      simpa [y] using hx
    have he : p y = p x := by rw [h y hy]; simp [y]
    simpa [p.injective he] using hy
  · intro hx
    rw [h x hx]
    exact l.formPerm_apply_mem_of_mem hx

lemma Follows.sameCycle {p : Perm α} {l : List α} (h : Follows p l)
    (hd : l.Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l) : p.SameCycle x y := by
  apply sameCycle_map l.formPerm p id _ (hd.isCycleOn_formPerm.2 hx hy)
  intro z
  by_cases hz : z ∈ l
  · change p.SameCycle z (l.formPerm z)
    rw [← h z hz]
    exact SameCycle.apply_right SameCycle.rfl
  · simp only [id_eq, List.formPerm_apply_of_notMem hz]
    exact SameCycle.rfl

omit [Fintype α] in
lemma formPerm_map_apply [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (l : List α) (x : α) :
    (l.map f).formPerm (f x) = f (l.formPerm x) := by
  induction l with
  | nil => simp only [List.map_nil, List.formPerm_nil, coe_one, id_eq]
  | cons a l ih =>
    cases l with
    | nil => simp only [List.map_cons, List.map_nil, List.formPerm_singleton, coe_one, id_eq]
    | cons b l =>
      change swap (f a) (f b) (((b :: l).map f).formPerm (f x)) =
        f (swap a b ((b :: l).formPerm x))
      rw [ih]
      exact (hf.map_swap a b _).symm

omit [Fintype α] in
lemma Follows.map_sum_left {p : Perm α} {q : Perm β} {l : List α}
    (h : Follows p l) : Follows (Equiv.sumCongr p q) (l.map Sum.inl) := by
  classical
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  simpa only [Equiv.sumCongr_apply, Sum.map_inl,
    formPerm_map_apply Sum.inl Sum.inl_injective] using congrArg Sum.inl (h x hx)

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse51} {β : Type portUniverse52} {A : Type portUniverse53} [Fintype α] [Fintype β] [CommGroup A]

@[simp] lemma sumCongr_sameCycle_inl (p : Perm α) (q : Perm β) (x y : α) :
    SameCycle (Equiv.sumCongr p q) (.inl x) (.inl y) ↔ p.SameCycle x y := by
  change (SameCycle.setoid (Equiv.sumCongr p q)).r _ _ ↔ _
  rw [sumCongr_cycles_setoid]
  exact sumSetoid_inl _ _ _ _

@[simp] lemma sumCongr_sameCycle_inr (p : Perm α) (q : Perm β) (x y : β) :
    SameCycle (Equiv.sumCongr p q) (.inr x) (.inr y) ↔ q.SameCycle x y := by
  change (SameCycle.setoid (Equiv.sumCongr p q)).r _ _ ↔ _
  rw [sumCongr_cycles_setoid]
  exact sumSetoid_inr _ _ _ _

@[simp] lemma sumCongr_not_sameCycle (p : Perm α) (q : Perm β) (x : α) (y : β) :
    ¬ SameCycle (Equiv.sumCongr p q) (.inl x) (.inr y) := by
  change ¬ (SameCycle.setoid (Equiv.sumCongr p q)).r _ _
  rw [sumCongr_cycles_setoid]
  exact sumSetoid_cross _ _ _ _

lemma prod_cycle_sum_left (p : Perm α) (q : Perm β) (x : α) (f : α ⊕ β → A) :
    ∏ y ∈ cycleSet (Equiv.sumCongr p q) (cycleClass _ (.inl x)), f y =
      ∏ y ∈ cycleSet p (cycleClass p x), f (.inl y) := by
  simp only [cycleSet, Finset.prod_filter, cycleClass_eq, Fintype.prod_sum_type,
    sumCongr_sameCycle_inl, sameCycle_comm (x := Sum.inr _), sumCongr_not_sameCycle,
    ↓reduceIte, Finset.prod_const_one, mul_one]

lemma prod_cycle_sum_right (p : Perm α) (q : Perm β) (x : β) (f : α ⊕ β → A) :
    ∏ y ∈ cycleSet (Equiv.sumCongr p q) (cycleClass _ (.inr x)), f y =
      ∏ y ∈ cycleSet q (cycleClass q x), f (.inr y) := by
  simp only [cycleSet, Finset.prod_filter, cycleClass_eq, Fintype.prod_sum_type,
    sumCongr_sameCycle_inr, sumCongr_not_sameCycle,
    ↓reduceIte, Finset.prod_const_one, one_mul]

def cycleInl (p : Perm α) (q : Perm β) : Cycles p → Cycles (Equiv.sumCongr p q) :=
  Quotient.map Sum.inl (fun _ _ h => (sumCongr_sameCycle_inl p q _ _).mpr h)

@[simp] lemma cycleInl_class (p : Perm α) (q : Perm β) (x : α) :
    cycleInl p q (cycleClass p x) = cycleClass _ (.inl x) := rfl

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse54}

lemma Follows.append_rotate {p : Perm α} {l m : List α} (h : Follows p (l ++ m))
    (hd : (l ++ m).Nodup) : Follows p (m ++ l) := by
  intro x hx
  have hx' : x ∈ l ++ m := by simpa only [List.mem_append, or_comm] using hx
  rw [h x hx', List.formPerm_eq_of_isRotated hd List.isRotated_append]

lemma Follows.split {p : Perm α} {a b : α} {l m : List α}
    (h : Follows p ((a :: l) ++ (b :: m))) (hd : ((a :: l) ++ (b :: m)).Nodup) :
    Follows (swap a b * p) (a :: l) ∧ Follows (swap a b * p) (b :: m) := by
  classical
  have hdis : List.Disjoint (a :: l) (b :: m) := by
    intro x hx hy
    exact (List.nodup_append.mp hd).2.2 x hx x hy rfl
  have hb : b ∉ a :: l := fun hb => hdis hb (by simp only [List.mem_cons, true_or])
  have heq (x : α) (hx : x ∈ (a :: l) ++ (b :: m)) :
      (swap a b * p) x = (a :: l).formPerm ((b :: m).formPerm x) := by
    rw [Perm.mul_apply, h x hx, formPerm_append_nonempty a b l m hb]
    simp only [Perm.mul_apply, swap_apply_self]
  constructor
  · intro x hx
    have hx' : x ∉ b :: m := fun hx' => hdis hx hx'
    rw [heq x (List.mem_append_left _ hx), List.formPerm_apply_of_notMem hx']
  · intro x hx
    rw [heq x (List.mem_append_right _ hx)]
    apply List.formPerm_apply_of_notMem
    exact fun hx' => hdis hx' ((b :: m).formPerm_apply_mem_of_mem hx)

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse55} {β : Type portUniverse56}

lemma Follows.map_sum_right {p : Perm α} {q : Perm β} {l : List β}
    (h : Follows q l) : Follows (Equiv.sumCongr p q) (l.map Sum.inr) := by
  classical
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  simpa only [Equiv.sumCongr_apply, Sum.map_inr,
    formPerm_map_apply Sum.inr Sum.inr_injective] using congrArg Sum.inr (h x hx)

lemma Follows.merge {p : Perm α} {a b : α} {l m : List α}
    (hl : Follows p (a :: l)) (hm : Follows p (b :: m))
    (hdis : List.Disjoint (a :: l) (b :: m)) :
    Follows (swap a b * p) ((a :: l) ++ (b :: m)) := by
  classical
  have hb : b ∉ a :: l := fun hb => hdis hb (by simp only [List.mem_cons, true_or])
  intro x hx
  rw [formPerm_append_nonempty a b l m hb]
  simp only [Perm.mul_apply]
  apply congrArg (swap a b)
  rcases List.mem_append.mp hx with hx | hx
  · rw [List.formPerm_apply_of_notMem (fun h => hdis hx h)]
    exact hl x hx
  · rw [List.formPerm_apply_of_notMem (fun h => hdis h ((b :: m).formPerm_apply_mem_of_mem hx))]
    exact hm x hx

end OddKaplansky.Planar
namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse57}

lemma follows_formPerm [DecidableEq α] (l : List α) : Follows l.formPerm l := by
  intro x _
  exact congrArg (fun d : DecidableEq α => @List.formPerm α d l x)
    (Subsingleton.elim _ _)

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse58} {B : Type portUniverse59} [Group B]

noncomputable def listPotential [DecidableEq α] (l : List α) (w : α → B) (x : α) : B :=
  ((l.take (l.idxOf x)).map w).prod

lemma listPotential_get [DecidableEq α] (l : List α) (hd : l.Nodup) (w : α → B)
    (i : ℕ) (hi : i < l.length) :
    listPotential l w l[i] = ((l.take i).map w).prod := by
  simp only [listPotential, hd.idxOf_getElem i hi]

lemma listPrefix_succ (l : List α) (w : α → B) (i : ℕ) (hi : i < l.length) :
    ((l.take (i+1)).map w).prod = ((l.take i).map w).prod * w l[i] := by
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.prod_append,
    List.map_singleton, List.prod_singleton]

lemma listPotential_balance_at [DecidableEq α] (l : List α) (hd : l.Nodup)
    (w : α → B) (i : ℕ) (hi : i + 1 < l.length) :
    listPotential l w (l.formPerm l[i]) = listPotential l w l[i] * w l[i] := by
  rw [List.formPerm_apply_lt_getElem l hd i hi, listPotential_get l hd w (i+1),
    listPotential_get l hd w i, listPrefix_succ]

lemma listPotential_end_at [DecidableEq α] (l : List α) (hd : l.Nodup)
    (w : α → B) (i : ℕ) (hi : i < l.length) (hend : i+1 = l.length) :
    listPotential l w (l.formPerm l[i]) = 1 ∧
      listPotential l w l[i] * w l[i] = (l.map w).prod := by
  constructor
  · rw [List.formPerm_apply_getElem l hd i hi]
    have hm : (i+1) % l.length = 0 := by rw [hend, Nat.mod_self]
    simp only [hm]
    rw [listPotential_get l hd w 0]
    rfl
  · rw [listPotential_get l hd w i, ← listPrefix_succ l w i hi, hend, List.take_length]

lemma listPotential_balance [DecidableEq α] (l : List α) (hd : l.Nodup)
    (w : α → B) (hprod : (l.map w).prod = 1) (x : α) (hx : x ∈ l) :
    listPotential l w (l.formPerm x) = listPotential l w x * w x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  by_cases hn : i+1 < l.length
  · exact listPotential_balance_at l hd w i hn
  · have he := listPotential_end_at l hd w i hi (by omega)
    rw [he.1, he.2, hprod]

def listDefect [Fintype α] [DecidableEq α] (l : List α) (hd : l.Nodup) (hall : ∀ x, x ∈ l)
    (w : α → B) (hprod : (l.map w).prod ≠ 1) : Holonomy.Defect l.formPerm w := by
  have hn : 0 < l.length := by
    by_contra h
    have he : l = [] := List.length_eq_zero_iff.mp (by omega)
    simp only [he, List.map_nil, List.prod_nil, ne_eq, not_true_eq_false] at hprod
  let e := l[l.length-1]'(by omega)
  refine ⟨listPotential l w, e, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hall x)
    apply listPotential_balance_at l hd w i
    by_contra h
    have he : i = l.length-1 := by omega
    exact hx (by simp only [he, e])
  · have he := listPotential_end_at l hd w (l.length-1) (by omega) (by omega)
    change listPotential l w (l.formPerm e) ≠ listPotential l w e * w e
    rw [show listPotential l w (l.formPerm e) = 1 from he.1,
      show listPotential l w e * w e = (l.map w).prod from he.2]
    exact Ne.symm hprod

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse60} {β : Type portUniverse61} {V : Type portUniverse62} {F : Type portUniverse63} {A : Type portUniverse64} {B : Type portUniverse65} [Fintype α] [Fintype β] [CommGroup A] [Group B]

def augInc (Inc : V → F → Prop) : Option V → F → Prop
  | none, _ => True
  | some v, f => Inc v f

def augMap (ι : V → F → (A →* B)) : Option V → F → (A →* B)
  | none, _ => 1
  | some v, f => ι v f

structure OpenBalanced (R : Ribbon α) (Inc : V → F → Prop) (ι : V → F → (A →* B))
    extends NoncommBalanced R (augInc Inc) (augMap ι) where
  potential_none : ∀ x, blackLabel x = none → potential x = 1
  exception_some : blackLabel exception ≠ none

structure FlatOpenBalanced (R : Ribbon α) (Inc : V → F → Prop) (ι : V → F → (A →* B)) where
  blackLabel : α → Option V
  whiteLabel : α → F
  blackLabel_rot : ∀ a, blackLabel (R.black a) = blackLabel a
  whiteLabel_rot : ∀ a, whiteLabel (R.white a) = whiteLabel a
  incident : ∀ a, augInc Inc (blackLabel a) (whiteLabel a)
  weight : α → A
  white_prod : ∀ c : Cycles R.white, ∏ a ∈ cycleSet R.white c, weight a = 1
  potential : α → B
  black_balance : ∀ a,
    potential (R.black a) = potential a * augMap ι (blackLabel a) (whiteLabel a) (weight a)
  potential_none : ∀ x, blackLabel x = none → potential x = 1

variable {R : Ribbon α} {S : Ribbon β} {Inc : V → F → Prop} {ι : V → F → (A →* B)}

def OpenBalanced.sumZero (D : OpenBalanced R Inc ι) (E : FlatOpenBalanced S Inc ι) :
    OpenBalanced (R.sum S) Inc ι where
  blackLabel := Sum.elim D.blackLabel E.blackLabel
  whiteLabel := Sum.elim D.whiteLabel E.whiteLabel
  blackLabel_rot := by rintro (x | x); exact D.blackLabel_rot x; exact E.blackLabel_rot x
  whiteLabel_rot := by rintro (x | x); exact D.whiteLabel_rot x; exact E.whiteLabel_rot x
  incident := by rintro (x | x); exact D.incident x; exact E.incident x
  weight := Sum.elim D.weight E.weight
  white_prod c := by
    dsimp only [Ribbon.sum] at c ⊢
    induction c using Quotient.inductionOn with
    | h x =>
      cases x with
      | inl x =>
        change (∏ a ∈ cycleSet (Equiv.sumCongr R.white S.white) (cycleClass _ (.inl x)), Sum.elim D.weight E.weight a) = 1
        rw [prod_cycle_sum_left]
        exact D.white_prod _
      | inr x =>
        change (∏ a ∈ cycleSet (Equiv.sumCongr R.white S.white) (cycleClass _ (.inr x)), Sum.elim D.weight E.weight a) = 1
        rw [prod_cycle_sum_right]
        exact E.white_prod _
  potential := Sum.elim D.potential E.potential
  exception := .inl D.exception
  black_balance := by
    rintro (x | x) hx
    · exact D.black_balance x (fun h => hx (congrArg Sum.inl h))
    · exact E.black_balance x
  black_defect := D.black_defect
  potential_none := by rintro (x | x); exact D.potential_none x; exact E.potential_none x
  exception_some := D.exception_some

def OpenBalanced.joinNone (D : OpenBalanced R Inc ι) (a b : α)
    (ha : D.blackLabel a = none) (hb : D.blackLabel b = none) :
    OpenBalanced (R.swapBlack a b) Inc ι where
  toNoncommBalanced := D.toNoncommBalanced.spliceBlack a b (ha.trans hb.symm)
    (D.toNoncommBalanced.defect.swapEqual a b
      ((D.potential_none a ha).trans (D.potential_none b hb).symm))
  potential_none := D.potential_none
  exception_some := D.exception_some

def OpenBalanced.fill (D : OpenBalanced R Inc ι)
    (l : List α) (hd : l.Nodup) (hrot : Follows R.black l)
    (hnone : ∀ x ∈ l, D.blackLabel x = none) (v : V)
    (hinc : ∀ x ∈ l, Inc v (D.whiteLabel x))
    (hprod : (l.map fun x => ι v (D.whiteLabel x) (D.weight x)).prod = 1) :
    OpenBalanced R Inc ι := by
  classical
  let w := fun x => ι v (D.whiteLabel x) (D.weight x)
  have he : D.exception ∉ l := fun h => D.exception_some (hnone _ h)
  have hep : R.black D.exception ∉ l := by simpa only [hrot.invariant] using he
  refine {
    blackLabel := fun x => if x ∈ l then some v else D.blackLabel x
    whiteLabel := D.whiteLabel
    blackLabel_rot := ?_
    whiteLabel_rot := D.whiteLabel_rot
    incident := ?_
    weight := D.weight
    white_prod := D.white_prod
    potential := fun x => if x ∈ l then listPotential l w x else D.potential x
    exception := D.exception
    black_balance := ?_
    black_defect := ?_
    potential_none := ?_
    exception_some := ?_ }
  · intro x; simp only [hrot.invariant, D.blackLabel_rot]
  · intro x
    by_cases hx : x ∈ l
    · simpa only [if_pos hx, augInc] using hinc x hx
    · simpa only [if_neg hx] using D.incident x
  · intro x hx
    by_cases hxl : x ∈ l
    · simp only [hrot.invariant, hxl, ite_true, augMap]
      rw [hrot x hxl]
      exact listPotential_balance l hd w hprod x hxl
    · simp only [hrot.invariant, hxl, ite_false]
      exact D.black_balance x hx
  · simpa only [if_neg he, if_neg hep] using D.black_defect
  · intro x hx
    by_cases hxl : x ∈ l
    · simp only [if_pos hxl] at hx
      exact (Option.some_ne_none v hx).elim
    · simp only [if_neg hxl] at hx ⊢
      exact D.potential_none x hx
  · simpa only [if_neg he] using D.exception_some

structure OpenDiagram (Inc : V → F → Prop) (ι : V → F → (A →* B))
    (f₀ : F) (w : List (F × A)) where
  Edge : Type
  fintype : Fintype Edge
  ribbon : Ribbon Edge
  balanced : @OpenBalanced Edge V F A B fintype _ _ ribbon Inc ι
  planar : @Ribbon.GenusZero Edge fintype ribbon
  anchor : Edge
  boundary : List Edge
  nodup : (anchor :: boundary).Nodup
  rotation : Follows ribbon.black (anchor :: boundary)
  exposed : ∀ x, balanced.blackLabel x = none ↔ x ∈ anchor :: boundary
  anchor_weight : balanced.weight anchor = 1
  anchor_label : balanced.whiteLabel anchor = f₀
  word : boundary.map (fun x => (balanced.whiteLabel x, balanced.weight x)) = w

attribute [instance] OpenDiagram.fintype

omit [Fintype α] [Fintype β] in
 def OpenDiagram.close (f₀ : F) (D : OpenDiagram Inc ι f₀ [])
    (v₀ : V) (hv : Inc v₀ f₀) : NoncommBalanced D.ribbon Inc ι := by
  have hb : D.boundary = [] := List.map_eq_nil_iff.mp D.word
  have hn (x : D.Edge) : D.balanced.blackLabel x = none ↔ x = D.anchor := by
    simpa only [hb, List.mem_cons, List.not_mem_nil, or_false] using D.exposed x
  let bl : D.Edge → V := fun x => (D.balanced.blackLabel x).getD v₀
  have heval (x : D.Edge) : ι (bl x) (D.balanced.whiteLabel x) (D.balanced.weight x) =
      augMap ι (D.balanced.blackLabel x) (D.balanced.whiteLabel x) (D.balanced.weight x) := by
    cases h : D.balanced.blackLabel x with
    | none =>
      have hx := (hn x).mp h
      rw [hx, D.anchor_weight]
      simp only [map_one]
    | some v => simp only [h, Option.getD_some, augMap, bl]
  exact {
    blackLabel := bl
    whiteLabel := D.balanced.whiteLabel
    blackLabel_rot := fun x => congrArg (fun v => v.getD v₀) (D.balanced.blackLabel_rot x)
    whiteLabel_rot := D.balanced.whiteLabel_rot
    incident := fun x => by
      cases h : D.balanced.blackLabel x with
      | none =>
        have hx := (hn x).mp h
        have hanc := (hn D.anchor).mpr rfl
        simpa only [hx, hanc, Option.getD_none, D.anchor_label, bl] using hv
      | some v =>
        have hi := D.balanced.incident x
        simpa only [h, Option.getD_some, augInc, bl] using hi
    weight := D.balanced.weight
    white_prod := D.balanced.white_prod
    potential := D.balanced.potential
    exception := D.balanced.exception
    black_balance := fun x hx => by simpa only [heval] using D.balanced.black_balance x hx
    black_defect := by simpa only [heval] using D.balanced.black_defect }

omit [Fintype α] [Fintype β] in
 theorem OpenDiagram.not_empty (f₀ : F) (D : OpenDiagram Inc ι f₀ [])
    (v₀ : V) (hv : Inc v₀ f₀) (hshort : ShortWords Inc ι)
    (hgirth : 8 ≤ (incidenceGraph Inc).egirth) : False :=
  (D.close f₀ v₀ hv).not_genusZero hshort hgirth D.planar

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse66} {V : Type portUniverse67} {F : Type portUniverse68} {A : Type portUniverse69} {B : Type portUniverse70} [Fintype α] [CommGroup A] [Group B]

lemma cycleSet_wheel_white (p : Perm α) (x : α ⊕ α) :
    cycleSet (Ribbon.wheel p).white (cycleClass _ x) =
      {Sum.inl (sumIndex x), Sum.inr (sumIndex x)} := by
  ext y
  rw [mem_cycleSet, cycleClass_eq]
  change (SameCycle.setoid (Ribbon.wheel p).white).r y x ↔ _
  rw [wheel_white_setoid]
  cases x <;> cases y <;> simp only [Setoid.ker_def, sumIndex, Sum.elim_inl, id_eq, Finset.mem_insert, Sum.inl.injEq, Finset.mem_singleton, reduceCtorEq, or_false, Sum.elim_inr, Sum.inr.injEq, false_or]

variable {Inc : V → F → Prop} {ι : V → F → (A →* B)}

def FlatOpenBalanced.wheel (p : Perm α) (v : V) (fl : α → F) (w : α → A)
    (hinc : ∀ x, Inc v (fl x)) (t : α → B)
    (ht : ∀ x, t (p x) = t x * ι v (fl x) (w x)) :
    FlatOpenBalanced (Ribbon.wheel p) Inc ι where
  blackLabel := Sum.elim (fun _ => none) (fun _ => some v)
  whiteLabel := Sum.elim fl fl
  blackLabel_rot := by rintro (x | x) <;> rfl
  whiteLabel_rot := by rintro (x | x) <;> rfl
  incident := by rintro (x | x); trivial; exact hinc x
  weight := Sum.elim w (fun x => (w x)⁻¹)
  white_prod c := by
    induction c using Quotient.inductionOn with
    | h x =>
      change (∏ y ∈ cycleSet (Ribbon.wheel p).white (cycleClass _ x), Sum.elim w (fun x => (w x)⁻¹) y) = 1
      rw [cycleSet_wheel_white, Finset.prod_pair (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])]
      simp only [Sum.elim_inl, Sum.elim_inr, mul_inv_cancel]
  potential := Sum.elim (fun _ => 1) (fun x => t (p x))
  black_balance := by
    rintro (x | x)
    · simp only [Ribbon.wheel, Equiv.sumCongr_apply, coe_inv, Sum.map_inl, Sum.elim_inl, augMap, MonoidHom.one_apply, mul_one]
    · change t (p (p⁻¹ x)) = t (p x) * ι v (fl x) ((w x)⁻¹)
      simp only [coe_inv, apply_symm_apply, ht x, map_inv, mul_assoc, mul_inv_cancel, mul_one]
  potential_none := by rintro (x | x) hx; rfl; exact (Option.some_ne_none v hx).elim

def OpenBalanced.wheel (p : Perm α) (v : V) (fl : α → F) (w : α → A)
    (hinc : ∀ x, Inc v (fl x)) (D : Holonomy.Defect p (fun x => ι v (fl x) (w x))) :
    OpenBalanced (Ribbon.wheel p) Inc ι where
  blackLabel := Sum.elim (fun _ => none) (fun _ => some v)
  whiteLabel := Sum.elim fl fl
  blackLabel_rot := by rintro (x | x) <;> rfl
  whiteLabel_rot := by rintro (x | x) <;> rfl
  incident := by rintro (x | x); trivial; exact hinc x
  weight := Sum.elim w (fun x => (w x)⁻¹)
  white_prod c := by
    induction c using Quotient.inductionOn with
    | h x =>
      change (∏ y ∈ cycleSet (Ribbon.wheel p).white (cycleClass _ x), Sum.elim w (fun x => (w x)⁻¹) y) = 1
      rw [cycleSet_wheel_white, Finset.prod_pair (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])]
      simp only [Sum.elim_inl, Sum.elim_inr, mul_inv_cancel]
  potential := Sum.elim (fun _ => 1) (fun x => D.potential (p x))
  exception := .inr D.exception
  black_balance := by
    rintro (x | x) hx
    · simp only [Ribbon.wheel, Equiv.sumCongr_apply, coe_inv, Sum.map_inl, Sum.elim_inl, augMap, MonoidHom.one_apply, mul_one]
    · have hx' : x ≠ D.exception := fun h => hx (congrArg Sum.inr h)
      change D.potential (p (p⁻¹ x)) = D.potential (p x) * ι v (fl x) ((w x)⁻¹)
      simp only [coe_inv, apply_symm_apply, D.balance x hx', map_inv, mul_assoc, mul_inv_cancel, mul_one]
  black_defect := by
    change D.potential (p (p⁻¹ D.exception)) ≠ D.potential (p D.exception) *
      ι v (fl D.exception) ((w D.exception)⁻¹)
    simp only [show p (p⁻¹ D.exception) = D.exception from p.apply_symm_apply _, map_inv]
    intro h
    apply D.defective
    have hh := congrArg (fun g => g * ι v (fl D.exception) (w D.exception)) h
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh.symm
  potential_none := by rintro (x | x) hx; rfl; exact (Option.some_ne_none v hx).elim
  exception_some := Option.some_ne_none v

omit [Fintype α] in
 def wordWheel (r : List (F × A)) (v : V)
    (hinc : ∀ t ∈ r, Inc v t.1)
    (hprod : (r.map (fun t => ι v t.1 t.2)).prod = 1) :
    FlatOpenBalanced (Ribbon.wheel (List.finRange r.length).formPerm) Inc ι :=
  FlatOpenBalanced.wheel _ v (fun i => (r.get i).1) (fun i => (r.get i).2)
    (fun i => hinc _ (List.get_mem r i))
    (listPotential (List.finRange r.length) (fun i => ι v (r.get i).1 (r.get i).2))
    (fun i => listPotential_balance _ (List.nodup_finRange _) _ (by
      change ((List.finRange r.length).map ((fun t : F × A => ι v t.1 t.2) ∘ r.get)).prod = 1
      rw [← List.map_map, List.map_get_finRange]
      exact hprod) i (by simp only [List.mem_finRange]))

omit [Fintype α] in
 def OpenDiagram.initial (f₀ : F) (v : V) (hf₀ : Inc v f₀) (w : List (F × A))
    (hinc : ∀ t ∈ w, Inc v t.1)
    (hprod : (w.map (fun t => ι v t.1 t.2)).prod ≠ 1) :
    OpenDiagram Inc ι f₀ w := by
  classical
  let r := (f₀, (1 : A)) :: w
  let n := w.length + 1
  let p := (List.finRange n).formPerm
  let fl := fun i : Fin n => (r.get i).1
  let wt := fun i : Fin n => (r.get i).2
  have hr : ∀ i : Fin n, Inc v (fl i) := by
    intro i
    have hm := List.get_mem r i
    rcases List.mem_cons.mp hm with h | h
    · simpa only [fl, h] using hf₀
    · exact hinc _ h
  have hp : ((List.finRange n).map (fun i => ι v (fl i) (wt i))).prod ≠ 1 := by
    change ((List.finRange r.length).map (fun i => ι v (r.get i).1 (r.get i).2)).prod ≠ 1
    change ((List.finRange r.length).map ((fun t : F × A => ι v t.1 t.2) ∘ r.get)).prod ≠ 1
    rw [← List.map_map, List.map_get_finRange]
    simpa only [r, List.map_cons, List.prod_cons, map_one, one_mul] using hprod
  let E := listDefect (List.finRange n) (List.nodup_finRange n) (fun i => by simp only [List.mem_finRange])
    (fun i => ι v (fl i) (wt i)) hp
  let D := OpenBalanced.wheel (ι := ι) p v fl wt hr E
  let bd : List (Fin n ⊕ Fin n) := (List.finRange w.length).map (Sum.inl ∘ Fin.succ)
  have heq : Sum.inl (0 : Fin n) :: bd = (List.finRange n).map Sum.inl := by
    change Sum.inl (0 : Fin (w.length+1)) :: bd = (List.finRange (w.length+1)).map Sum.inl
    rw [List.finRange_succ, List.map_cons, List.map_map]
  refine {
    Edge := Fin n ⊕ Fin n
    fintype := inferInstance
    ribbon := Ribbon.wheel p
    balanced := D
    planar := Ribbon.genusZero_wheel p
    anchor := Sum.inl (0 : Fin n)
    boundary := bd
    nodup := ?_
    rotation := ?_
    exposed := ?_
    anchor_weight := rfl
    anchor_label := rfl
    word := ?_ }
  · rw [heq]
    exact (List.nodup_finRange n).map Sum.inl_injective
  · rw [heq]
    exact (follows_formPerm (List.finRange n)).map_sum_left
  · intro x
    rw [heq]
    cases x <;> simp only [OpenBalanced.wheel, Sum.elim_inl, List.mem_map, List.mem_finRange, Sum.inl.injEq, true_and, exists_eq, D, Sum.elim_inr, reduceCtorEq, and_false, exists_const]
  · change bd.map (fun x => (D.whiteLabel x, D.weight x)) = w
    dsimp only [bd]
    rw [List.map_map]
    change ((List.finRange w.length).map (fun i => w.get i)) = w
    exact List.map_get_finRange w

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {V : Type portUniverse71} {F : Type portUniverse72} {A : Type portUniverse73} {B : Type portUniverse74} [CommGroup A] [Group B]
variable {Inc : V → F → Prop} {ι : V → F → (A →* B)} {f₀ : F} {w : List (F × A)}

theorem OpenDiagram.deleteBlock (D : OpenDiagram Inc ι f₀ w)
    (pre r post : List D.Edge) (hboundary : D.boundary = pre ++ r ++ post)
    (v : V) (hinc : ∀ x ∈ r, Inc v (D.balanced.whiteLabel x))
    (hprod : (r.map fun x => ι v (D.balanced.whiteLabel x) (D.balanced.weight x)).prod = 1) :
    Nonempty (OpenDiagram Inc ι f₀ ((pre ++ post).map
      (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)))) := by
  classical
  cases r with
  | nil =>
    have hw : w = (pre ++ post).map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) := by
      exact D.word.symm.trans (congrArg _ (by simpa only [List.append_nil] using hboundary))
    exact ⟨hw ▸ D⟩
  | cons a r =>
    let M := post ++ D.anchor :: pre
    have hM : M ≠ [] := by simp only [ne_eq, List.append_eq_nil_iff, reduceCtorEq, and_false, not_false_eq_true, M]
    obtain ⟨b, m, hbm⟩ := List.exists_cons_of_ne_nil hM
    have hrot : Follows D.ribbon.black ((D.anchor :: pre) ++ ((a :: r) ++ post)) := by
      simpa only [hboundary, List.cons_append, List.append_assoc] using D.rotation
    have hnd : (((D.anchor :: pre) ++ ((a :: r) ++ post))).Nodup := by
      simpa only [hboundary, List.cons_append, List.append_assoc] using D.nodup
    have hrot' : Follows D.ribbon.black ((a :: r) ++ (b :: m)) := by
      simpa only [List.append_assoc, ← hbm] using hrot.append_rotate hnd
    have hnd' : ((a :: r) ++ (b :: m)).Nodup := by
      have hn := (List.nodup_append_comm).mp hnd
      simpa only [List.append_assoc, ← hbm] using hn
    have hmem (x : D.Edge) : x ∈ D.anchor :: D.boundary ↔ x ∈ (a :: r) ++ (b :: m) := by
      simp only [hboundary, ← hbm, M, List.mem_cons, List.mem_append]
      first | (simp only [or_comm, or_left_comm, or_assoc]; done) | tauto
    have hab : D.ribbon.black.SameCycle a b := hrot'.sameCycle hnd'
      (by simp only [List.cons_append, List.mem_cons, List.mem_append, true_or]) (by simp only [List.cons_append, List.mem_cons, List.mem_append, true_or, or_true])
    have habne : a ≠ b := by
      intro h
      exact (List.nodup_append.mp hnd').2.2 a (by simp only [List.mem_cons, true_or]) b (by simp only [List.mem_cons, true_or]) h
    have ha : D.balanced.blackLabel a = none :=
      (D.exposed a).mpr ((hmem a).mpr (by simp only [List.cons_append, List.mem_cons, List.mem_append, true_or]))
    have hb : D.balanced.blackLabel b = none :=
      (D.exposed b).mpr ((hmem b).mpr (by simp only [List.cons_append, List.mem_cons, List.mem_append, true_or, or_true]))
    let S := D.ribbon.swapBlack a b
    have hsplit := hrot'.split hnd'
    have hnone : ∀ x ∈ a :: r, D.balanced.blackLabel x = none := by
      intro x hx
      exact (D.exposed x).mpr ((hmem x).mpr (List.mem_append_left _ hx))
    let E := (D.balanced.joinNone a b ha hb).fill (a :: r)
      (List.nodup_append.mp hnd').1 hsplit.1 hnone v hinc hprod
    have hmrot : Follows S.black (D.anchor :: (pre ++ post)) := by
      have hh : Follows S.black (post ++ (D.anchor :: pre)) := by
        simpa only [← hbm, S, Ribbon.swapBlack, M] using hsplit.2
      have hn : (post ++ (D.anchor :: pre)).Nodup := by
        simpa only [← hbm] using (List.nodup_append.mp hnd').2.1
      simpa only [List.cons_append] using hh.append_rotate hn
    have hmnd : (D.anchor :: (pre ++ post)).Nodup := by
      have hn : (post ++ (D.anchor :: pre)).Nodup := by
        simpa only [← hbm] using (List.nodup_append.mp hnd').2.1
      simpa only [List.cons_append] using List.nodup_append_comm.mp hn
    have hrem (x : D.Edge) : x ∈ b :: m ↔ x ∈ D.anchor :: (pre ++ post) := by
      simp only [← hbm, M, List.mem_append, List.mem_cons]
      first | (simp only [or_comm, or_left_comm, or_assoc]; done) | tauto
    exact ⟨{
      Edge := D.Edge
      fintype := inferInstance
      ribbon := S
      balanced := E
      planar := D.ribbon.genusZero_swapBlack_split D.planar a b habne hab
      anchor := D.anchor
      boundary := pre ++ post
      nodup := hmnd
      rotation := hmrot
      exposed := fun x => by
        change (if x ∈ a :: r then some v else D.balanced.blackLabel x) = none ↔ _
        by_cases hx : x ∈ a :: r
        · simp only [if_pos hx, Option.some_ne_none, false_iff]
          exact fun h => (List.nodup_append.mp hnd').2.2 x hx x ((hrem x).mpr h) rfl
        · rw [if_neg hx, D.exposed, hmem, List.mem_append]
          simpa only [hx, false_or] using hrem x
      anchor_weight := D.anchor_weight
      anchor_label := D.anchor_label
      word := rfl }⟩

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {V F A B : Type} [CommGroup A] [Group B]
variable {Inc : V → F → Prop} {ι : V → F → (A →* B)}
variable {f₀ : F} {w : List (F × A)}

theorem OpenDiagram.insertBlock (D : OpenDiagram Inc ι f₀ w)
    (pre post : List D.Edge) (hboundary : D.boundary = pre ++ post)
    (r : List (F × A)) (v : V) (hinc : ∀ t ∈ r, Inc v t.1)
    (hprod : (r.map (fun t => ι v t.1 t.2)).prod = 1) :
    Nonempty (OpenDiagram Inc ι f₀
      (pre.map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) ++ r ++
        post.map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)))) := by
  classical
  by_cases hr : r = []
  · subst r
    have hw : w = pre.map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) ++
        [] ++ post.map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) := by
      exact D.word.symm.trans (by rw [hboundary, List.map_append, List.append_nil])
    exact ⟨hw ▸ D⟩
  let p := (List.finRange r.length).formPerm
  let W := wordWheel r v hinc hprod
  let T := D.ribbon.sum (Ribbon.wheel p)
  let E := D.balanced.sumZero W
  let f : D.Edge → D.Edge ⊕ (Fin r.length ⊕ Fin r.length) := Sum.inl
  let g : Fin r.length → D.Edge ⊕ (Fin r.length ⊕ Fin r.length) := Sum.inr ∘ Sum.inl
  let Q := (List.finRange r.length).map g
  let M := (post ++ D.anchor :: pre).map f
  have hqn : Q ≠ [] := by
    intro he
    have hh : r.length = 0 := by simpa only [Q, List.length_map, List.length_finRange, List.length_nil] using congrArg List.length he
    exact hr (List.length_eq_zero_iff.mp hh)
  have hmn : M ≠ [] := by simp only [List.map_append, List.map_cons, ne_eq, List.append_eq_nil_iff, List.map_eq_nil_iff, reduceCtorEq, and_false, not_false_eq_true, M]
  obtain ⟨a, l, hqa⟩ := List.exists_cons_of_ne_nil hqn
  obtain ⟨b, m, hmb⟩ := List.exists_cons_of_ne_nil hmn
  have hnd₀ : ((D.anchor :: pre) ++ post).Nodup := by
    simpa only [hboundary, List.cons_append] using D.nodup
  have hrot₀ : Follows D.ribbon.black ((D.anchor :: pre) ++ post) := by
    simpa only [hboundary, List.cons_append] using D.rotation
  have hndM : M.Nodup := (List.nodup_append_comm.mp hnd₀).map Sum.inl_injective
  have hndQ : Q.Nodup := (List.nodup_finRange _).map (Sum.inr_injective.comp Sum.inl_injective)
  have hM : Follows T.black M := by
    exact (hrot₀.append_rotate hnd₀).map_sum_left
  have hQ : Follows T.black Q := by
    have h : Follows (Ribbon.wheel p).black ((List.finRange r.length).map Sum.inl) :=
      (follows_formPerm (List.finRange r.length)).map_sum_left
    simpa only [List.map_map, T, Ribbon.sum, Q, g] using h.map_sum_right (p := D.ribbon.black)
  have hdis : List.Disjoint Q M := by
    intro x hx hy
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hy
    exact Sum.inl_ne_inr (show (Sum.inl j : D.Edge ⊕ (Fin r.length ⊕ Fin r.length)) = Sum.inr (Sum.inl i) from hj)
  have hnd : (Q ++ M).Nodup := List.Nodup.append hndQ hndM hdis
  have hac : a ∈ Q := by rw [hqa]; simp only [List.mem_cons, true_or]
  have hbc : b ∈ M := by rw [hmb]; simp only [List.mem_cons, true_or]
  have hcomp : ¬ T.components.r a b := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hac
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hbc
    rw [Ribbon.sum_components]
    exact fun h => sumSetoid_cross _ _ j (Sum.inl i)
      ((sumSetoid D.ribbon.components (Ribbon.wheel p).components).iseqv.symm h)
  have hal : E.blackLabel a = none := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hac
    rfl
  have hbl : E.blackLabel b = none := by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hbc
    apply (D.exposed j).mpr
    simpa only [hboundary, List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using hj
  let S := T.swapBlack a b
  let Z := E.joinNone a b hal hbl
  have hrot : Follows S.black (Q ++ M) := by
    simp only [hqa, hmb] at hQ hM hdis ⊢
    exact hQ.merge hM hdis
  have hrot' : Follows S.black (f D.anchor :: (pre.map f ++ Q ++ post.map f)) := by
    have hh : Follows S.black ((Q ++ post.map f) ++ (f D.anchor :: pre.map f)) := by
      simpa only [M, List.map_append, List.map_cons, List.append_assoc] using hrot
    have hn : ((Q ++ post.map f) ++ (f D.anchor :: pre.map f)).Nodup := by
      simpa only [M, List.map_append, List.map_cons, List.append_assoc] using hnd
    simpa only [List.cons_append, List.append_assoc] using hh.append_rotate hn
  have hnd' : (f D.anchor :: (pre.map f ++ Q ++ post.map f)).Nodup := by
    have hn : ((Q ++ post.map f) ++ (f D.anchor :: pre.map f)).Nodup := by
      simpa only [M, List.map_append, List.map_cons, List.append_assoc] using hnd
    simpa only [List.cons_append, List.append_assoc] using List.nodup_append_comm.mp hn
  refine ⟨{
    Edge := D.Edge ⊕ (Fin r.length ⊕ Fin r.length)
    fintype := inferInstance
    ribbon := S
    balanced := Z
    planar := T.genusZero_swapBlack_merge (D.ribbon.genusZero_sum (Ribbon.wheel p) D.planar
      (Ribbon.genusZero_wheel p)) a b hcomp
    anchor := f D.anchor
    boundary := pre.map f ++ Q ++ post.map f
    nodup := hnd'
    rotation := hrot'
    exposed := ?_
    anchor_weight := D.anchor_weight
    anchor_label := D.anchor_label
    word := ?_ }⟩
  · rintro (x | (i | i))
    · change D.balanced.blackLabel x = none ↔ _
      rw [D.exposed, hboundary]
      simp only [List.mem_cons, List.mem_append, Function.comp_def, List.append_assoc, Sum.inl.injEq, List.mem_map, exists_eq_right, List.mem_finRange, reduceCtorEq, and_false, exists_false, false_or, f, Q, g]
    · change (none : Option V) = none ↔ _
      simp only [Function.comp_def, List.append_assoc, List.mem_cons, reduceCtorEq, List.mem_append, List.mem_map, and_false, exists_false, List.mem_finRange, Sum.inr.injEq, Sum.inl.injEq, true_and, exists_eq, or_false, or_true, f, Q, g]
    · change (some v : Option V) = none ↔ _
      simp only [reduceCtorEq, Function.comp_def, List.append_assoc, List.mem_cons, List.mem_append, List.mem_map, and_false, exists_false, List.mem_finRange, Sum.inr.injEq, or_self, f, Q, g]
  · change (pre.map f ++ Q ++ post.map f).map
        (fun x => (E.whiteLabel x, E.weight x)) = _
    simp only [List.map_append, List.map_map]
    congr 2
    dsimp only [Q]
    rw [List.map_map]
    change ((List.finRange r.length).map (fun i => r.get i)) = r
    exact List.map_get_finRange r

end OddKaplansky.Planar

namespace OddKaplansky.Planar
variable {V F A B : Type} [CommGroup A] [Group B]
variable {Inc : V → F → Prop} {ι : V → F → (A →* B)} {f₀ : F}

theorem OpenDiagram.deleteWordBlock (pre r post : List (F × A))
    (v : V) (hinc : ∀ t ∈ r, Inc v t.1)
    (hprod : (r.map (fun t => ι v t.1 t.2)).prod = 1)
    (D : OpenDiagram Inc ι f₀ (pre ++ r ++ post)) :
    Nonempty (OpenDiagram Inc ι f₀ (pre ++ post)) := by
  classical
  obtain ⟨p, q, hpq, hp, hq⟩ := List.map_eq_append_iff.mp
    (D.word.trans (List.append_assoc pre r post))
  obtain ⟨s, t, hst, hs, ht⟩ := List.map_eq_append_iff.mp hq
  have hboundary : D.boundary = p ++ s ++ t := by
    exact hpq.trans ((congrArg (p ++ ·) hst).trans (List.append_assoc p s t).symm)
  have hnd : s.Nodup := by
    have hh := D.nodup.tail
    rw [hboundary] at hh
    exact (List.nodup_append.mp (List.nodup_append.mp hh).1).2.1
  have hinc' : ∀ x ∈ s, Inc v (D.balanced.whiteLabel x) := by
    intro x hx
    apply hinc (D.balanced.whiteLabel x, D.balanced.weight x)
    simpa only [hs] using (List.mem_map_of_mem (f := fun x =>
      (D.balanced.whiteLabel x, D.balanced.weight x)) hx)
  have hprod' : (s.map fun x =>
      ι v (D.balanced.whiteLabel x) (D.balanced.weight x)).prod = 1 := by
    have hh := hprod
    rw [← hs, List.map_map] at hh
    exact hh
  obtain ⟨E⟩ := D.deleteBlock p s t hboundary v hinc' hprod'
  have he : (p ++ t).map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) =
      pre ++ post := by rw [List.map_append, hp, ht]
  exact ⟨he ▸ E⟩

theorem OpenDiagram.insertWordBlock (pre r post : List (F × A))
    (v : V) (hinc : ∀ t ∈ r, Inc v t.1)
    (hprod : (r.map (fun t => ι v t.1 t.2)).prod = 1)
    (D : OpenDiagram Inc ι f₀ (pre ++ post)) :
    Nonempty (OpenDiagram Inc ι f₀ (pre ++ r ++ post)) := by
  obtain ⟨p, q, hpq, hp, hq⟩ := List.map_eq_append_iff.mp D.word
  obtain ⟨E⟩ := D.insertBlock p q hpq r v hinc hprod
  rw [hp, hq] at E
  exact ⟨E⟩

end OddKaplansky.Planar

namespace OddKaplansky.WordReduction
variable {α : Type portUniverse75}
abbrev Word (α : Type portUniverse76) := List (α × Bool)

inductive Delete (Allowed : Word α → Prop) : Word α → Word α → Prop
  | block (pre r post : Word α) (hr : Allowed r) :
      Delete Allowed (pre ++ r ++ post) (pre ++ post)

abbrev Related (Allowed : Word α → Prop) := Relation.EqvGen (Delete Allowed)

variable {Allowed : Word α → Prop}

lemma rel_trans {u v w : Word α} (h₁ : Related Allowed u v) (h₂ : Related Allowed v w) :
    Related Allowed u w := Relation.EqvGen.trans _ _ _ h₁ h₂

lemma rel_symm {u v : Word α} (h : Related Allowed u v) :
    Related Allowed v u := Relation.EqvGen.symm _ _ h

lemma Related.append_left {u v : Word α} (h : Related Allowed u v) (w : Word α) :
    Related Allowed (w ++ u) (w ++ v) := by
  induction h with
  | rel x y h =>
    cases h with
    | block pre r post hr =>
      simpa only [List.append_assoc] using Relation.EqvGen.rel _ _ (Delete.block (w ++ pre) r post hr)
  | refl x => exact .refl _
  | symm _ _ _ ih => exact rel_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact rel_trans ih₁ ih₂

lemma Related.append_right {u v : Word α} (h : Related Allowed u v) (w : Word α) :
    Related Allowed (u ++ w) (v ++ w) := by
  induction h with
  | rel x y h =>
    cases h with
    | block pre r post hr =>
      simpa only [List.append_assoc] using Relation.EqvGen.rel _ _ (Delete.block pre r (post ++ w) hr)
  | refl x => exact .refl _
  | symm _ _ _ ih => exact rel_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact rel_trans ih₁ ih₂

lemma Related.inv (hinv : ∀ w, Allowed w → Allowed (FreeGroup.invRev w))
    {u v : Word α} (h : Related Allowed u v) :
    Related Allowed (FreeGroup.invRev u) (FreeGroup.invRev v) := by
  induction h with
  | rel x y h =>
    cases h with
    | block pre r post hr =>
      simpa only [FreeGroup.invRev_append, List.append_assoc] using
        Relation.EqvGen.rel _ _ (Delete.block (FreeGroup.invRev post) (FreeGroup.invRev r)
          (FreeGroup.invRev pre) (hinv r hr))
  | refl x => exact .refl _
  | symm _ _ _ ih => exact rel_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact rel_trans ih₁ ih₂

lemma related_of_red_step
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)])
    {u v : Word α} (h : FreeGroup.Red.Step u v) : Related Allowed u v := by
  cases h with
  | @not pre post a b =>
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using Relation.EqvGen.rel _ _ (Delete.block pre [(a, b), (a, !b)] post (hcancel a b))

lemma related_of_red
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)])
    {u v : Word α} (h : FreeGroup.Red u v) : Related Allowed u v := by
  induction h with
  | refl => exact .refl _
  | tail h hstep ih => exact rel_trans ih (related_of_red_step hcancel hstep)

lemma related_of_mk_eq
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)])
    {u v : Word α} (h : FreeGroup.mk u = FreeGroup.mk v) : Related Allowed u v := by
  obtain ⟨w, huw, hvw⟩ := FreeGroup.Red.exact.mp h
  exact rel_trans (related_of_red hcancel huw) (rel_symm (related_of_red hcancel hvw))

lemma related_append_null {u v : Word α} (hu : Related Allowed u [])
    (hv : Related Allowed v []) : Related Allowed (u ++ v) [] := by
  exact rel_trans (hu.append_right v) (by simpa only [List.nil_append] using hv)

def nullSubgroup (Allowed : Word α → Prop)
    (hinv : ∀ w, Allowed w → Allowed (FreeGroup.invRev w)) : Subgroup (FreeGroup α) where
  carrier g := ∃ w : Word α, FreeGroup.mk w = g ∧ Related Allowed w []
  one_mem' := ⟨[], rfl, .refl _⟩
  mul_mem' := by
    rintro _ _ ⟨u, rfl, hu⟩ ⟨v, rfl, hv⟩
    exact ⟨u ++ v, FreeGroup.mul_mk.symm, related_append_null hu hv⟩
  inv_mem' := by
    rintro _ ⟨w, rfl, hw⟩
    exact ⟨FreeGroup.invRev w, FreeGroup.inv_mk.symm, by simpa only [FreeGroup.invRev_empty] using hw.inv hinv⟩

lemma nullSubgroup_normal
    (hinv : ∀ w, Allowed w → Allowed (FreeGroup.invRev w))
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)]) :
    (nullSubgroup Allowed hinv).Normal := by
  constructor
  rintro g ⟨w, rfl, hw⟩ u
  induction u using Quot.inductionOn with
  | h v =>
    change ∃ z, FreeGroup.mk z = FreeGroup.mk v * FreeGroup.mk w * (FreeGroup.mk v)⁻¹ ∧ _
    refine ⟨v ++ w ++ FreeGroup.invRev v, ?_, ?_⟩
    · rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
    · have h₁ := (hw.append_left v).append_right (FreeGroup.invRev v)
      simp only [List.append_nil] at h₁
      apply rel_trans h₁
      apply related_of_mk_eq hcancel
      rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
      simp only [mul_inv_cancel, ← FreeGroup.one_eq_mk]

theorem of_presented_eq_one (rels : Set (FreeGroup α))
    (hinv : ∀ w, Allowed w → Allowed (FreeGroup.invRev w))
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)])
    (hrels : ∀ g ∈ rels, ∃ w : Word α, FreeGroup.mk w = g ∧ Allowed w)
    (w : Word α) (hw : PresentedGroup.mk rels (FreeGroup.mk w) = 1) :
    Related Allowed w [] := by
  let H := nullSubgroup Allowed hinv
  let : H.Normal := nullSubgroup_normal hinv hcancel
  have hle : Subgroup.normalClosure rels ≤ H := by
    apply Subgroup.normalClosure_le_normal
    intro g hg
    obtain ⟨v, hv, hA⟩ := hrels g hg
    refine ⟨v, hv, ?_⟩
    simpa only [List.nil_append, List.append_nil] using Relation.EqvGen.rel _ _ (Delete.block [] v [] hA)
  obtain ⟨v, hv, hnull⟩ := hle (PresentedGroup.mk_eq_one_iff.mp hw)
  exact rel_trans (related_of_mk_eq hcancel hv.symm) hnull

end OddKaplansky.WordReduction

namespace OddKaplansky.Planar
variable {V F A B X : Type} [CommGroup A] [Group B]
variable {Inc : V → F → Prop} {ι : V → F → (A →* B)} {f₀ : F}

theorem OpenDiagram.related_iff (token : X × Bool → F × A)
    (Allowed : List (X × Bool) → Prop)
    (hA : ∀ r, Allowed r → ∃ v, (∀ t ∈ r.map token, Inc v t.1) ∧
      ((r.map token).map (fun t => ι v t.1 t.2)).prod = 1)
    {u w : List (X × Bool)} (h : WordReduction.Related Allowed u w) :
    Nonempty (OpenDiagram Inc ι f₀ (u.map token)) ↔
      Nonempty (OpenDiagram Inc ι f₀ (w.map token)) := by
  induction h with
  | rel u w h =>
    cases h with
    | block pre r post hr =>
      obtain ⟨v, hi, hs⟩ := hA r hr
      simp only [List.map_append]
      constructor
      · rintro ⟨D⟩
        exact D.deleteWordBlock _ _ _ v hi hs
      · rintro ⟨D⟩
        exact D.insertWordBlock _ _ _ v hi hs
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end OddKaplansky.Planar

namespace OddKaplansky.GluedGroup
noncomputable section
open scoped Classical
variable {V F A B : Type} [CommGroup A] [Group B]
variable (Inc : V → F → Prop) (ι : V → F → (A →* B))

abbrev Generator := F × A
abbrev LocalGenerator (v : V) := {s : Generator (F := F) (A := A) // Inc v s.1}

def includeLocal (v : V) : FreeGroup (LocalGenerator (A := A) Inc v) →*
    FreeGroup (Generator (F := F) (A := A)) := FreeGroup.map Subtype.val

def localEvaluation (v : V) : FreeGroup (LocalGenerator (A := A) Inc v) →* B :=
  FreeGroup.lift (fun s => ι v s.val.1 s.val.2)

def relators : Set (FreeGroup (Generator (F := F) (A := A))) :=
  {g | ∃ (v : V) (w : FreeGroup (LocalGenerator (A := A) Inc v)),
    localEvaluation Inc ι v w = 1 ∧ includeLocal Inc v w = g}

abbrev N := PresentedGroup (relators Inc ι)

def fromLocal (v : V) : FreeGroup (LocalGenerator (A := A) Inc v) →* N Inc ι :=
  (PresentedGroup.mk (relators Inc ι)).comp (includeLocal Inc v)

lemma local_kernel_le (v : V) : (localEvaluation Inc ι v).ker ≤ (fromLocal Inc ι v).ker := by
  intro w hw
  exact PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure ⟨v, w, hw, rfl⟩)

def signedToken (s : Generator (F := F) (A := A) × Bool) : F × A :=
  (s.1.1, if s.2 then s.1.2 else s.1.2⁻¹)

def Allowed (w : List (Generator (F := F) (A := A) × Bool)) : Prop :=
  ∃ v : V, (∀ t ∈ w.map signedToken, Inc v t.1) ∧
    ((w.map signedToken).map (fun t => ι v t.1 t.2)).prod = 1

lemma signedToken_inv (s : Generator (F := F) (A := A) × Bool) :
    signedToken (s.1, !s.2) = ((signedToken s).1, (signedToken s).2⁻¹) := by
  rcases s with ⟨s, b⟩
  cases b <;> simp only [signedToken, Bool.not_false, ↓reduceIte, Prod.mk.eta, Bool.false_eq_true, inv_inv, Bool.not_true]

lemma allowed_inv (w : List (Generator (F := F) (A := A) × Bool))
    (h : Allowed Inc ι w) : Allowed Inc ι (FreeGroup.invRev w) := by
  obtain ⟨v, hi, hp⟩ := h
  refine ⟨v, ?_, ?_⟩
  · intro t ht
    simp only [FreeGroup.invRev, List.map_reverse, List.map_map, List.mem_reverse,
      List.mem_map] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    change Inc v (signedToken (s.1, !s.2)).1
    rw [signedToken_inv]
    exact hi (signedToken s) (List.mem_map_of_mem hs)
  · simp only [FreeGroup.invRev, List.map_reverse, List.map_map, Function.comp_def,
      signedToken_inv, map_inv]
    have hinv : ((w.map (fun s => (ι v (signedToken s).1 (signedToken s).2)⁻¹)).reverse).prod =
        ((w.map (fun s => ι v (signedToken s).1 (signedToken s).2)).prod)⁻¹ := by
      clear hi hp
      induction w with
      | nil => simp only [List.map_nil, List.reverse_nil, List.prod_nil, inv_one]
      | cons a w ih => simp only [List.map_cons, List.reverse_cons, List.prod_append, ih, List.prod_cons, List.prod_nil, mul_one, mul_inv_rev]
    rw [hinv]
    simpa only [List.map_map, Function.comp_def, inv_eq_one] using hp

lemma allowed_cancel (hInc : ∀ f, ∃ v, Inc v f)
    (g : Generator (F := F) (A := A)) (b : Bool) :
    Allowed Inc ι [(g, b), (g, !b)] := by
  obtain ⟨v, hv⟩ := hInc g.1
  refine ⟨v, ?_, ?_⟩
  · intro t ht
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> exact hv
  · cases b <;> simp only [Bool.not_false, List.map_cons, signedToken, Bool.false_eq_true, ↓reduceIte, Prod.mk.eta, List.map_nil, map_inv, List.prod_cons, List.prod_nil, mul_one, inv_mul_cancel, Bool.not_true, mul_inv_cancel]

lemma localEvaluation_word (v : V) (w : List (LocalGenerator (A := A) Inc v × Bool)) :
    localEvaluation Inc ι v (FreeGroup.mk w) =
      ((w.map (fun s => (s.1.val, s.2))).map (fun s =>
        ι v (signedToken s).1 (signedToken s).2)).prod := by
  rw [localEvaluation, FreeGroup.lift_mk, List.map_map]
  congr 1
  apply List.map_congr_left
  intro s _
  rcases s with ⟨s, b⟩
  cases b <;> simp only [cond_false, signedToken, Function.comp_apply, Bool.false_eq_true, ↓reduceIte, map_inv, cond_true]

lemma relators_allowed (g : FreeGroup (Generator (F := F) (A := A)))
    (hg : g ∈ relators Inc ι) :
    ∃ w, FreeGroup.mk w = g ∧ Allowed Inc ι w := by
  obtain ⟨v, r, he, rfl⟩ := hg
  induction r using Quot.inductionOn with
  | h w =>
    refine ⟨w.map (fun s => (s.1.val, s.2)), rfl, v, ?_, ?_⟩
    · intro t ht
      simp only [List.map_map, List.mem_map] at ht
      obtain ⟨s, _, rfl⟩ := ht
      exact s.1.property
    · change localEvaluation Inc ι v (FreeGroup.mk w) = 1 at he
      simpa only [localEvaluation_word, List.map_map, Function.comp_def] using he

theorem fromLocal_eq_one_iff (hInc : ∀ f, ∃ v, Inc v f)
    (hshort : Planar.ShortWords Inc ι)
    (hgirth : 8 ≤ (Planar.incidenceGraph Inc).egirth)
    (v : V) (w : FreeGroup (LocalGenerator (A := A) Inc v)) :
    fromLocal Inc ι v w = 1 ↔ localEvaluation Inc ι v w = 1 := by
  refine ⟨?_, fun h => local_kernel_le Inc ι v h⟩
  intro hw
  by_contra he
  induction w using Quot.inductionOn with
  | h w =>
    have hp : ((w.map (fun s => (s.1.val, s.2))).map
        (fun s => ι v (signedToken s).1 (signedToken s).2)).prod ≠ 1 := by
      change localEvaluation Inc ι v (FreeGroup.mk w) ≠ 1 at he
      simpa only [localEvaluation_word] using he
    have hne : w ≠ [] := by rintro rfl; simp only [List.map_nil, List.prod_nil, ne_eq, not_true_eq_false] at hp
    obtain ⟨s, z, rfl⟩ := List.exists_cons_of_ne_nil hne
    let q := (s :: z).map (fun s => (s.1.val, s.2))
    have hq : WordReduction.Related (Allowed Inc ι) q [] :=
      WordReduction.of_presented_eq_one (relators Inc ι)
        (allowed_inv Inc ι) (allowed_cancel Inc ι hInc)
        (relators_allowed Inc ι) q hw
    have hi : Nonempty (Planar.OpenDiagram Inc ι s.1.val.1 (q.map signedToken)) := by
      refine ⟨Planar.OpenDiagram.initial _ v s.1.property _ ?_ ?_⟩
      · intro t ht
        simp only [q, List.map_map, List.mem_map] at ht
        obtain ⟨a, _, rfl⟩ := ht
        exact a.1.property
      · simpa only [q, List.map_map, Function.comp_def] using hp
    obtain ⟨D⟩ := (Planar.OpenDiagram.related_iff (Inc := Inc) (ι := ι)
      (f₀ := s.1.val.1) signedToken (Allowed Inc ι) (fun _ h => h) hq).mp hi
    exact D.not_empty _ v s.1.property hshort hgirth

abbrev Local (v : V) := (localEvaluation Inc ι v).range

def theta (v : V) : Local Inc ι v →* N Inc ι :=
  (localEvaluation Inc ι v).rangeRestrict.liftOfSurjective
    (localEvaluation Inc ι v).rangeRestrict_surjective
    ⟨fromLocal Inc ι v, by
      intro w hw
      apply local_kernel_le Inc ι v
      exact congrArg Subtype.val hw⟩

lemma theta_evaluation (v : V) (w : FreeGroup (LocalGenerator (A := A) Inc v)) :
    theta Inc ι v ((localEvaluation Inc ι v).rangeRestrict w) = fromLocal Inc ι v w := by
  simp only [theta, MonoidHom.liftOfSurjective, MonoidHom.liftOfRightInverse_comp_apply]

theorem theta_injective (hInc : ∀ f, ∃ v, Inc v f)
    (hshort : Planar.ShortWords Inc ι) (hgirth : 8 ≤ (Planar.incidenceGraph Inc).egirth)
    (v : V) : Function.Injective (theta Inc ι v) := by
  apply (theta Inc ι v).ker_eq_bot_iff.mp
  apply bot_unique
  intro a ha
  change a = 1
  obtain ⟨w, rfl⟩ := (localEvaluation Inc ι v).rangeRestrict_surjective a
  apply Subtype.ext
  apply (fromLocal_eq_one_iff Inc ι hInc hshort hgirth v w).mp
  simpa only [MonoidHom.mem_ker, theta_evaluation] using ha

end
end OddKaplansky.GluedGroup

namespace OddKaplansky.GluedGroup
open scoped Classical
variable {V F A B : Type} [CommGroup A] [Group B]
variable (Inc : V → F → Prop) (ι : V → F → (A →* B))

noncomputable def localEdge (v : V) (f : F) (hf : Inc v f) (a : A) : Local Inc ι v :=
  (localEvaluation Inc ι v).rangeRestrict (FreeGroup.of ⟨(f, a), hf⟩)

@[simp] lemma localEdge_val (v : V) (f : F) (hf : Inc v f) (a : A) :
    (localEdge Inc ι v f hf a : B) = ι v f a := by
  change localEvaluation Inc ι v (FreeGroup.of ⟨(f, a), hf⟩) = ι v f a
  simp only [localEvaluation, FreeGroup.lift_apply_of]

@[simp] lemma theta_localEdge (v : V) (f : F) (hf : Inc v f) (a : A) :
    theta Inc ι v (localEdge Inc ι v f hf a) = PresentedGroup.of (f, a) := by
  rw [localEdge, theta_evaluation]
  simp only [fromLocal, includeLocal, MonoidHom.coe_comp, Function.comp_apply, FreeGroup.map.of, PresentedGroup.of]
end OddKaplansky.GluedGroup

end
end
end

end OAI
end

section
namespace OAI


section
noncomputable section
open scoped Classical
open Monoid Function
namespace OddKaplansky.MultipleHNN

variable {H : Type u} [Group H] {I : Type v}
variable (A B : I → Subgroup H) (φ : ∀ i, A i ≃* B i)

def con : Con (Monoid.Coprod H (FreeGroup I)) := conGen fun x y =>
  ∃ (i : I) (a : A i), x = Coprod.inr (FreeGroup.of i) * Coprod.inl (a : H) ∧
    y = Coprod.inl (φ i a : H) * Coprod.inr (FreeGroup.of i)

def Extension := (con A B φ).Quotient

instance : Group (Extension A B φ) := by delta Extension; infer_instance

def of : H →* Extension A B φ := (con A B φ).mk'.comp Coprod.inl

def letter (i : I) : Extension A B φ := (con A B φ).mk' (Coprod.inr (FreeGroup.of i))

lemma letter_mul_of (i : I) (a : A i) :
    letter A B φ i * of A B φ a = of A B φ (φ i a) * letter A B φ i :=
  (Con.eq _).mpr <| ConGen.Rel.of _ _ ⟨i, a, rfl, rfl⟩

def lift {G : Type portUniverse1} [Group G] (f : H →* G) (t : I → G)
    (ht : ∀ i (a : A i), t i * f a = f (φ i a) * t i) : Extension A B φ →* G :=
  Con.lift _ (Coprod.lift f (FreeGroup.lift t)) (Con.conGen_le.mpr (by
    rintro _ _ ⟨i, a, rfl, rfl⟩
    simp only [Con.ker_rel, map_mul, Coprod.lift_apply_inr, FreeGroup.lift_apply_of, Coprod.lift_apply_inl, ht]))

@[simp] lemma lift_of {G : Type portUniverse2} [Group G] (f : H →* G) (t : I → G)
    (ht : ∀ i (a : A i), t i * f a = f (φ i a) * t i) (h : H) :
    lift A B φ f t ht (of A B φ h) = f h := by
  change Coprod.lift f (FreeGroup.lift t) (Coprod.inl h) = f h
  simp only [Coprod.lift_apply_inl]

@[simp] lemma lift_letter {G : Type portUniverse3} [Group G] (f : H →* G) (t : I → G)
    (ht : ∀ i (a : A i), t i * f a = f (φ i a) * t i) (i : I) :
    lift A B φ f t ht (letter A B φ i) = t i := by
  change Coprod.lift f (FreeGroup.lift t) (Coprod.inr (FreeGroup.of i)) = t i
  simp only [Coprod.lift_apply_inr, FreeGroup.lift_apply_of]

theorem finite_partial_realization (S : Finset I) :
    ∃ (G : Type (max u v)) (_ : Group G) (f : H →* G),
      Function.Injective f ∧ ∃ t : I → G,
        ∀ i ∈ S, ∀ a : A i, t i * f a = f (φ i a) * t i := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨ULift.{v} H, inferInstance, (MulEquiv.ulift : ULift.{v} H ≃* H).symm.toMonoidHom,
      (MulEquiv.ulift : ULift.{v} H ≃* H).symm.injective, fun _ => 1, ?_⟩
    simp
  | @insert i S hi ih =>
    obtain ⟨G, hG, f, hf, t, ht⟩ := ih
    let fA := (A i).equivMapOfInjective f hf
    let fB := (B i).equivMapOfInjective f hf
    let ψ : (A i).map f ≃* (B i).map f := fA.symm.trans ((φ i).trans fB)
    let E := HNNExtension G ((A i).map f) ((B i).map f) ψ
    let emb : G →* E := HNNExtension.of
    let t' : I → E := fun j => if j = i then HNNExtension.t else emb (t j)
    refine ⟨E, inferInstance, emb.comp f,
      (HNNExtension.of_injective ψ).comp hf, t', ?_⟩
    intro j hj a
    rcases Finset.mem_insert.mp hj with rfl | hj
    · have h := HNNExtension.t_mul_of (φ := ψ) (fA a)
      simpa [t', fA, fB, ψ, emb] using h
    · by_cases hji : j = i
      · subst j
        have h := HNNExtension.t_mul_of (φ := ψ) (fA a)
        simpa [t', fA, fB, ψ, emb] using h
      · simpa [t', hji, ← map_mul] using congrArg emb (ht j hj a)

theorem of_injective [Fintype I] : Function.Injective (of A B φ) := by
  obtain ⟨G, hG, f, hf, t, ht⟩ := finite_partial_realization A B φ Finset.univ
  intro x y h
  apply hf
  have h' := congrArg (lift A B φ f t (fun i a => ht i (Finset.mem_univ i) a)) h
  simpa only [lift_of] using h'

@[elab_as_elim]
theorem induction_on {P : Extension A B φ → Prop} (x : Extension A B φ)
    (hof : ∀ h, P (of A B φ h)) (ht : ∀ i, P (letter A B φ i))
    (hmul : ∀ x y, P x → P y → P (x * y)) (hinv : ∀ x, P x → P x⁻¹) : P x := by
  change ∀ left right : (con A B φ).Quotient, P left → P right → P (left * right) at hmul
  change ∀ element : (con A B φ).Quotient, P element → P element⁻¹ at hinv
  change ∀ element : H, P ((con A B φ).mk' (Coprod.inl element)) at hof
  obtain ⟨w, rfl⟩ := (Con.mk'_surjective (c := con A B φ)) x
  induction w using Coprod.induction_on with
  | inl h => exact hof h
  | inr w =>
    induction w using FreeGroup.induction_on with
    | C1 => simpa only [map_one] using hof 1
    | of i => exact ht i
    | inv_of i ih =>
      change P ((con A B φ).mk' (Coprod.inr ((FreeGroup.of i)⁻¹)))
      rw [map_inv, map_inv]
      exact hinv _ ih
    | mul a b ha hb => simpa only [map_mul] using hmul _ _ ha hb
  | mul a b ha hb => simpa only [map_mul] using hmul _ _ ha hb

instance [Finite I] [Group.FG H] : Group.FG (Extension A B φ) := by
  obtain ⟨S, hS, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG H)
  let T : Set (Extension A B φ) := of A B φ '' S ∪ Set.range (letter A B φ)
  apply Group.fg_iff.mpr
  refine ⟨T, ?_, (hfin.image _).union (Set.finite_range _)⟩
  apply top_unique
  intro x hxTop
  clear hxTop
  induction x using induction_on A B φ with
  | hof h =>
    have hh : h ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top h
    induction hh using Subgroup.closure_induction with
    | mem h hh => exact Subgroup.subset_closure (Or.inl ⟨h, hh, rfl⟩)
    | one => simp only [map_one, one_mem]
    | mul h k _ _ hh hk => simpa only [map_mul] using (Subgroup.closure T).mul_mem hh hk
    | inv h _ hh => simpa only [map_inv, inv_mem_iff] using (Subgroup.closure T).inv_mem hh
  | ht i => exact Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  | hmul x y hx hy => exact (Subgroup.closure T).mul_mem hx hy
  | hinv x hx => exact (Subgroup.closure T).inv_mem hx

end OddKaplansky.MultipleHNN

namespace OddKaplansky.StarAmalgam
open Monoid
variable {I G : Type} [Group G] {D S : I → Type}
variable [∀ i, Group (D i)] [∀ i, Group (S i)]
variable (f : ∀ i, S i →* G) (g : ∀ i, S i →* D i)

abbrev Free := Coprod G (CoprodI D)

def con : Con (Free (G := G) (D := D)) := conGen fun x y =>
  ∃ (i : I) (s : S i), x = Coprod.inl (f i s) ∧ y = Coprod.inr (CoprodI.of (g i s))

def Amalgam := (con f g).Quotient
instance : _root_.Group (Amalgam f g) := by delta Amalgam; infer_instance

def ofBase : G →* Amalgam f g := (con f g).mk'.comp Coprod.inl

def ofFactor (i : I) : D i →* Amalgam f g :=
  (con f g).mk'.comp (Coprod.inr.comp CoprodI.of)

lemma identify (i : I) (s : S i) : ofBase f g (f i s) = ofFactor f g i (g i s) :=
  (Con.eq _).mpr <| ConGen.Rel.of _ _ ⟨i, s, rfl, rfl⟩

def lift {E : Type portUniverse4} [_root_.Group E] (b : G →* E) (d : ∀ i, D i →* E)
    (h : ∀ i s, b (f i s) = d i (g i s)) : Amalgam f g →* E :=
  Con.lift _ (Coprod.lift b (CoprodI.lift d)) (Con.conGen_le.mpr (by
    rintro _ _ ⟨i, s, rfl, rfl⟩
    simp only [Con.ker_rel, Coprod.lift_apply_inl, h, Coprod.lift_apply_inr, CoprodI.lift_of]))

@[simp] lemma lift_base {E : Type portUniverse5} [_root_.Group E] (b : G →* E) (d : ∀ i, D i →* E)
    (h : ∀ i s, b (f i s) = d i (g i s)) (x : G) :
    lift f g b d h (ofBase f g x) = b x := by
  change Coprod.lift b (CoprodI.lift d) (Coprod.inl x) = b x
  simp only [Coprod.lift_apply_inl]

@[simp] lemma lift_factor {E : Type portUniverse6} [_root_.Group E] (b : G →* E) (d : ∀ i, D i →* E)
    (h : ∀ i s, b (f i s) = d i (g i s)) (i : I) (x : D i) :
    lift f g b d h (ofFactor f g i x) = d i x := by
  change Coprod.lift b (CoprodI.lift d) (Coprod.inr (CoprodI.of x)) = d i x
  simp only [Coprod.lift_apply_inr, CoprodI.lift_of]

theorem faithful_realization [Fintype I]
    (hf : ∀ i, Function.Injective (f i)) (hg : ∀ i, Function.Injective (g i)) :
    ∃ (E : Type) (_ : _root_.Group E) (b : G →* E) (d : ∀ i, D i →* E),
      Function.Injective b ∧ (∀ i, Function.Injective (d i)) ∧
      ∀ i s, b (f i s) = d i (g i s) := by
  let a : ∀ i, S i →* Free (G := G) (D := D) := fun i =>
    Coprod.inr.comp (CoprodI.of.comp (g i))
  let b₀ : ∀ i, S i →* Free (G := G) (D := D) := fun i => Coprod.inl.comp (f i)
  have ha : ∀ i, Function.Injective (a i) := fun i =>
    Coprod.inr_injective.comp ((CoprodI.of_injective i).comp (hg i))
  have hb : ∀ i, Function.Injective (b₀ i) := fun i => Coprod.inl_injective.comp (hf i)
  let ea : ∀ i, S i ≃* (a i).range := fun i =>
    MulEquiv.ofBijective (a i).rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.mpr (ha i), (a i).rangeRestrict_surjective⟩
  let eb : ∀ i, S i ≃* (b₀ i).range := fun i =>
    MulEquiv.ofBijective (b₀ i).rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.mpr (hb i), (b₀ i).rangeRestrict_surjective⟩
  let A := fun i => (a i).range
  let B := fun i => (b₀ i).range
  let φ : ∀ i, A i ≃* B i := fun i => (ea i).symm.trans (eb i)
  let E := MultipleHNN.Extension A B φ
  let emb : Free (G := G) (D := D) →* E := MultipleHNN.of A B φ
  have hemb : Function.Injective emb := MultipleHNN.of_injective A B φ
  let b : G →* E := emb.comp Coprod.inl
  let d : ∀ i, D i →* E := fun i =>
    (MulAut.conj (MultipleHNN.letter A B φ i)).toMonoidHom.comp
      (emb.comp (Coprod.inr.comp CoprodI.of))
  refine ⟨E, inferInstance, b, d, hemb.comp Coprod.inl_injective, ?_, ?_⟩
  · intro i
    exact (MulAut.conj _).injective.comp
      (hemb.comp (Coprod.inr_injective.comp (CoprodI.of_injective i)))
  · intro i s
    have h := MultipleHNN.letter_mul_of A B φ i (ea i s)
    have hφ : φ i (ea i s) = eb i s := by simp [φ]
    rw [hφ] at h
    change MultipleHNN.letter A B φ i * emb (a i s) =
      emb (b₀ i s) * MultipleHNN.letter A B φ i at h
    have hh := congrArg (fun x => x * (MultipleHNN.letter A B φ i)⁻¹) h
    simpa [b, d, a, b₀, mul_assoc] using hh.symm

variable [Fintype I]

theorem ofBase_injective (hf : ∀ i, Function.Injective (f i))
    (hg : ∀ i, Function.Injective (g i)) : Function.Injective (ofBase f g) := by
  obtain ⟨E, hE, b, d, hb, hd, h⟩ := faithful_realization f g hf hg
  intro x y hxy
  apply hb
  simpa only [lift_base] using congrArg (lift f g b d h) hxy

end OddKaplansky.StarAmalgam

end
end

end OAI
end

section
namespace OAI


section

namespace OddKaplansky.Gluing
noncomputable section
open scoped Classical
open Monoid
variable {V F A B : Type} [CommGroup A] [Group B]
variable (Inc : V → F → Prop) (ι : V → F → (A →* B))

def con : Con (CoprodI (fun _ : V => B)) := conGen fun x y =>
  ∃ (f : F) (v w : V) (a : A), Inc v f ∧ Inc w f ∧
    x = CoprodI.of (i := v) (ι v f a) ∧ y = CoprodI.of (i := w) (ι w f a)

def Q := (con Inc ι).Quotient
instance : Group (Q Inc ι) := by delta Q; infer_instance

def vertex (v : V) : B →* Q Inc ι := (con Inc ι).mk'.comp (CoprodI.of (M := fun _ : V => B) (i := v))

lemma edge_eq (f : F) (v w : V) (a : A) (hv : Inc v f) (hw : Inc w f) :
    vertex Inc ι v (ι v f a) = vertex Inc ι w (ι w f a) :=
  (Con.eq _).mpr <| ConGen.Rel.of _ _ ⟨f, v, w, a, hv, hw, rfl, rfl⟩

def lift {E : Type portUniverse1} [Group E] (d : V → B →* E)
    (hd : ∀ f v w a, Inc v f → Inc w f → d v (ι v f a) = d w (ι w f a)) : Q Inc ι →* E :=
  Con.lift _ (CoprodI.lift d) (Con.conGen_le.mpr (by
    rintro _ _ ⟨f, v, w, a, hv, hw, rfl, rfl⟩
    simpa only [Con.ker_rel, CoprodI.lift_of] using hd f v w a hv hw))

@[simp] lemma lift_vertex {E : Type portUniverse2} [Group E] (d : V → B →* E)
    (hd : ∀ f v w a, Inc v f → Inc w f → d v (ι v f a) = d w (ι w f a)) (v : V) (b : B) :
    lift Inc ι d hd (vertex Inc ι v b) = d v b := by
  change CoprodI.lift d (CoprodI.of (i := v) b) = d v b
  simp only [CoprodI.lift_of]

theorem vertex_injective [Fintype V] (hInc : ∀ f, ∃ v, Inc v f)
    (hshort : Planar.ShortWords Inc ι) (hgirth : 8 ≤ (Planar.incidenceGraph Inc).egirth)
    (v : V) : Function.Injective (vertex Inc ι v) := by
  let S := fun v => GluedGroup.Local Inc ι v
  let f : ∀ v, S v →* GluedGroup.N Inc ι := GluedGroup.theta Inc ι
  let g : ∀ v, S v →* B := fun v => (GluedGroup.localEvaluation Inc ι v).range.subtype
  obtain ⟨E, hE, b, d, hb, hd, he⟩ := StarAmalgam.faithful_realization f g
    (GluedGroup.theta_injective Inc ι hInc hshort hgirth) (fun _ => Subtype.val_injective)
  have heq : ∀ e v w a, Inc v e → Inc w e → d v (ι v e a) = d w (ι w e a) := by
    intro e v w a hv hw
    have hv' := he v (GluedGroup.localEdge Inc ι v e hv a)
    have hw' := he w (GluedGroup.localEdge Inc ι w e hw a)
    change b (GluedGroup.theta Inc ι v (GluedGroup.localEdge Inc ι v e hv a)) =
      d v (GluedGroup.localEdge Inc ι v e hv a : B) at hv'
    change b (GluedGroup.theta Inc ι w (GluedGroup.localEdge Inc ι w e hw a)) =
      d w (GluedGroup.localEdge Inc ι w e hw a : B) at hw'
    rw [GluedGroup.theta_localEdge, GluedGroup.localEdge_val] at hv' hw'
    exact hv'.symm.trans hw'
  intro x y hxy
  apply hd v
  simpa only [lift_vertex] using congrArg (lift Inc ι d heq) hxy

instance [Finite V] [Finite B] : Group.FG (Q Inc ι) := by
  let T : Set (Q Inc ι) := Set.range (fun x : V × B => vertex Inc ι x.1 x.2)
  apply Group.fg_iff.mpr
  refine ⟨T, ?_, Set.finite_range _⟩
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨w, rfl⟩ := (con Inc ι).mk'_surjective x
  induction w using CoprodI.induction_on with
  | one => rw [map_one]; exact (Subgroup.closure T).one_mem
  | of v b => exact Subgroup.subset_closure ⟨(v, b), rfl⟩
  | mul x y hx hy => rw [map_mul]; exact (Subgroup.closure T).mul_mem hx hy

end
end OddKaplansky.Gluing

end

end OAI
end

section
namespace OAI


section
noncomputable section
open scoped Classical
namespace OddKaplansky.Planar
variable {V : Type portUniverse1} {F : Type portUniverse2} (Inc : V → F → Prop)

def incidenceColoring : (incidenceGraph Inc).Coloring Bool :=
  SimpleGraph.Coloring.mk Sum.isLeft (by
    intro x y h
    cases x <;> cases y <;> simp_all [incidenceGraph])

lemma incidence_walk_even {u : V ⊕ F} (w : (incidenceGraph Inc).Walk u u) : Even w.length := by
  exact ((incidenceColoring Inc).even_length_iff_congr w).mpr Iff.rfl

lemma getVert_even_left {v : V} {z : V ⊕ F} (w : (incidenceGraph Inc).Walk (.inl v) z)
    (i : ℕ) (hi : 2*i ≤ w.length) : ∃ x : V, w.getVert (2*i)=.inl x := by
  have he : Even (w.take (2*i)).length := by rw [SimpleGraph.Walk.take_length,inf_eq_left.mpr hi]; exact even_two_mul i
  have hc := ((incidenceColoring Inc).even_length_iff_congr (w.take (2*i))).mp he
  cases hx : w.getVert (2*i) with
  | inl x => exact ⟨x,rfl⟩
  | inr f =>
    change (true = true ↔ Sum.isLeft (w.getVert (2*i)) = true) at hc
    rw [hx] at hc
    exact False.elim (Bool.noConfusion (hc.mp rfl))

lemma getVert_odd_right {v : V} {z : V ⊕ F} (w : (incidenceGraph Inc).Walk (.inl v) z)
    (i : ℕ) (hi : 2*i+1 ≤ w.length) : ∃ f : F, w.getVert (2*i+1)=.inr f := by
  obtain ⟨x,hx⟩ := getVert_even_left Inc w i (by omega)
  have ha := w.adj_getVert_succ (by omega : 2*i < w.length)
  rw [hx] at ha
  cases hf : w.getVert (2*i+1) with
  | inl y =>
    rw [hf] at ha
    exact False.elim ha
  | inr f => exact ⟨f,rfl⟩

lemma cycle_polygon_left {v : V} (w : (incidenceGraph Inc).Walk (.inl v) (.inl v))
    (hw : w.IsCycle) {k : ℕ} (hk : w.length=2*k) :
    ∃ (point : Fin k → V) (line : Fin k → F), Function.Injective point ∧ Function.Injective line ∧
      (∀ i, Inc (point i) (line i)) ∧ (∀ i, Inc (point (finRotate k i)) (line i)) := by
  have hkp : 0 < k := by have := hw.three_le_length; omega
  have hp (i : Fin k) := getVert_even_left Inc w i.val (by omega)
  have hl (i : Fin k) := getVert_odd_right Inc w i.val (by omega)
  let point (i : Fin k) := (hp i).choose
  let line (i : Fin k) := (hl i).choose
  have hpoint (i : Fin k) : w.getVert (2*i.val)=.inl (point i) := (hp i).choose_spec
  have hline (i : Fin k) : w.getVert (2*i.val+1)=.inr (line i) := (hl i).choose_spec
  have hnext (i : Fin k) : w.getVert (2*i.val+2)=.inl (point (finRotate k i)) := by
    have hk2 : 2 ≤ k := by have := hw.three_le_length; omega
    by_cases hi : i.val+1 < k
    · have hh : (finRotate k i).val=i.val+1 := by
        rw [finRotate_apply]
        exact Fin.val_add_one_of_lt' hi
      rw [show 2*i.val+2=2*(finRotate k i).val by omega]
      exact hpoint _
    · have hi' : i.val=k-1 := by omega
      have hrot : finRotate k i=⟨0,hkp⟩ := by
        apply Fin.ext
        rw [finRotate_apply,Fin.val_add]
        simp only [hi', Fin.coe_ofNat_eq_mod, Nat.add_mod_mod, Nat.sub_add_cancel (by omega : 1 ≤ k), Nat.mod_self]
      rw [show 2*i.val+2=w.length by omega,SimpleGraph.Walk.getVert_length,hrot]
      simpa only [Sum.inl.injEq, mul_zero, SimpleGraph.Walk.getVert_zero] using (hpoint ⟨0,hkp⟩)
  refine ⟨point,line,?_,?_,?_,?_⟩
  · intro i j hij
    apply Fin.ext
    have he := hw.getVert_injOn' (show 2*i.val ≤ w.length-1 by omega)
      (show 2*j.val ≤ w.length-1 by omega) ((hpoint i).trans ((congrArg Sum.inl hij).trans (hpoint j).symm))
    omega
  · intro i j hij
    apply Fin.ext
    have he := hw.getVert_injOn' (show 2*i.val+1 ≤ w.length-1 by omega)
      (show 2*j.val+1 ≤ w.length-1 by omega) ((hline i).trans ((congrArg Sum.inr hij).trans (hline j).symm))
    omega
  · intro i
    have ha := w.adj_getVert_succ (by omega : 2*i.val < w.length)
    rw [hpoint,hline] at ha
    exact ha
  · intro i
    have ha := w.adj_getVert_succ (by omega : 2*i.val+1 < w.length)
    rw [hline,show 2*i.val+1+1=2*i.val+2 by omega,hnext] at ha
    exact ha

lemma cycle_polygon {z : V ⊕ F} (w : (incidenceGraph Inc).Walk z z) (hw : w.IsCycle) :
    ∃ k, w.length=2*k ∧ 2 ≤ k ∧ ∃ (point : Fin k → V) (line : Fin k → F),
      Function.Injective point ∧ Function.Injective line ∧
      (∀ i, Inc (point i) (line i)) ∧ (∀ i, Inc (point (finRotate k i)) (line i)) := by
  obtain ⟨k,hk⟩ := incidence_walk_even Inc w
  have hk' : w.length=2*k := by omega
  refine ⟨k,hk',by have := hw.three_le_length; omega,?_⟩
  cases z with
  | inl v => exact cycle_polygon_left Inc w hw hk'
  | inr f =>
    have ha := w.adj_getVert_succ (by have := hw.three_le_length; omega : 0 < w.length)
    simp only [SimpleGraph.Walk.getVert_zero,zero_add] at ha
    cases hz : w.getVert 1 with
    | inr g =>
      rw [hz] at ha
      exact False.elim ha
    | inl v =>
      have hm : (.inl v : V ⊕ F) ∈ w.support := hz ▸ w.getVert_mem_support 1
      exact cycle_polygon_left Inc (w.rotate (.inl v) hm) (hw.rotate hm)
        ((w.length_rotate _ _).trans hk')

end OddKaplansky.Planar

end
end

end OAI
end

section
namespace OAI

section

namespace OddKaplansky.GraphEdges
noncomputable section
open scoped Classical
variable {V : Type} [LinearOrder V] (Γ : SimpleGraph V)

abbrev Edge := {e : V × V // e.1 < e.2 ∧ Γ.Adj e.1 e.2}
def Inc (v : V) (e : Edge Γ) : Prop := v = e.val.1 ∨ v = e.val.2

def neighbor (v : V) (e : Edge Γ) : V := if v = e.val.1 then e.val.2 else e.val.1

lemma incident_exists (e : Edge Γ) : ∃ v, Inc Γ v e := ⟨e.val.1, Or.inl rfl⟩
lemma endpoints_ne (e : Edge Γ) : e.val.1 ≠ e.val.2 := (ne_of_lt e.property.1)

lemma neighbor_incident (v : V) (e : Edge Γ) (_hv : Inc Γ v e) : Inc Γ (neighbor Γ v e) e := by
  simp only [neighbor, Inc]
  split_ifs <;> simp only [or_true, true_or]

lemma neighbor_ne (v : V) (e : Edge Γ) (hv : Inc Γ v e) : neighbor Γ v e ≠ v := by
  rcases hv with rfl | rfl <;> simp only [neighbor, ↓reduceIte, ne_eq, (endpoints_ne Γ e).symm, not_false_eq_true, endpoints_ne Γ e]

lemma endpoints_of_inc {v w : V} {e : Edge Γ} (hv : Inc Γ v e) (hw : Inc Γ w e)
    (hne : v ≠ w) : e.val = (v, w) ∨ e.val = (w, v) := by
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
  · exact (hne rfl).elim
  · exact Or.inl (Prod.eta _).symm
  · exact Or.inr (Prod.eta _).symm
  · exact (hne rfl).elim

lemma edge_eq_of_inc {v w : V} {e f : Edge Γ}
    (hev : Inc Γ v e) (hew : Inc Γ w e) (hfv : Inc Γ v f) (hfw : Inc Γ w f)
    (hne : v ≠ w) : e = f := by
  have he := endpoints_of_inc Γ hev hew hne
  have hf := endpoints_of_inc Γ hfv hfw hne
  rcases he with he | he <;> rcases hf with hf | hf
  · exact Subtype.ext (he.trans hf.symm)
  · have h₁ := e.property.1
    have h₂ := f.property.1
    rw [he] at h₁
    rw [hf] at h₂
    exact (lt_asymm h₁ h₂).elim
  · have h₁ := e.property.1
    have h₂ := f.property.1
    rw [he] at h₁
    rw [hf] at h₂
    exact (lt_asymm h₁ h₂).elim
  · exact Subtype.ext (he.trans hf.symm)

lemma neighbor_injective (v : V) : Function.Injective (fun e : {e : Edge Γ // Inc Γ v e} =>
    neighbor Γ v e.val) := by
  intro e f h
  change neighbor Γ v e.val = neighbor Γ v f.val at h
  apply Subtype.ext
  apply edge_eq_of_inc Γ e.property (neighbor_incident Γ v e.val e.property) f.property
  · rw [h]
    exact neighbor_incident Γ v f.val f.property
  · exact (neighbor_ne Γ v e.val e.property).symm

lemma adj_of_inc {v w : V} {e : Edge Γ} (hv : Inc Γ v e) (hw : Inc Γ w e) (hne : v ≠ w) :
    Γ.Adj v w := by
  have he := endpoints_of_inc Γ hv hw hne
  rcases he with he | he
  · simpa only [he] using e.property.2
  · exact (show Γ.Adj w v by simpa only [he] using e.property.2).symm

theorem incidence_girth (htri : ∀ a b c, Γ.Adj a b → Γ.Adj b c → Γ.Adj c a → False) :
    8 ≤ (Planar.incidenceGraph (Inc Γ)).egirth := by
  apply SimpleGraph.le_egirth.mpr
  intro z w hw
  obtain ⟨k, hk, hk2, point, line, hp, hl, hi, hn⟩ := Planar.cycle_polygon (Inc Γ) w hw
  have hk4 : 4 ≤ k := by
    by_contra hh
    have hk' : k = 2 ∨ k = 3 := by omega
    rcases hk' with rfl | rfl
    · have hv0 : Inc Γ (point 1) (line 0) := by simpa only [Fin.isValue, finRotate_apply, zero_add] using hn (0 : Fin 2)
      have hv1 : Inc Γ (point 0) (line 1) := by simpa only [Fin.isValue, finRotate_apply, Fin.reduceAdd] using hn (1 : Fin 2)
      have he := edge_eq_of_inc Γ (hi 0) hv0 hv1 (hi 1) (fun h => by have := hp h; simp only [Fin.isValue, zero_ne_one] at this)
      have hh := hl he
      exact (by decide : (0 : Fin 2) ≠ 1) hh
    · have h01 : Γ.Adj (point 0) (point 1) :=
        adj_of_inc Γ (hi 0) (by simpa only [Fin.isValue, finRotate_apply, zero_add] using hn (0 : Fin 3)) (fun h => by have := hp h; simp only [Fin.isValue, zero_ne_one] at this)
      have h12 : Γ.Adj (point 1) (point 2) :=
        adj_of_inc Γ (hi 1) (by simpa only [Fin.isValue, finRotate_apply, Fin.reduceAdd] using hn (1 : Fin 3)) (fun h => by have := hp h; simp only [Fin.isValue, Fin.reduceEq] at this)
      have h20 : Γ.Adj (point 2) (point 0) :=
        adj_of_inc Γ (hi 2) (by simpa only [Fin.isValue, finRotate_apply, Fin.reduceAdd] using hn (2 : Fin 3)) (fun h => by have := hp h; simp only [Fin.isValue, Fin.reduceEq] at this)
      exact htri _ _ _ h01 h12 h20
  exact_mod_cast (show 8 ≤ w.length by omega)

end
end OddKaplansky.GraphEdges

namespace OddKaplansky.SourceGraph
noncomputable section
open scoped Classical

@[ext] structure Vertex where
  val : Finset (Fin 1200)
  property : val.card = 600

def vertexEquiv : Vertex ≃ {s : Finset (Fin 1200) // s.card = 600} where
  toFun v := ⟨v.val, v.property⟩
  invFun s := ⟨s.val, s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Vertex := Fintype.ofEquiv _ vertexEquiv.symm
instance : LinearOrder Vertex := LinearOrder.lift' (fun s => s.val.sort) (by
  intro s t h
  apply Vertex.ext
  simpa only [Finset.sort_toFinset] using congrArg List.toFinset h)

lemma card_vertices : Fintype.card Vertex = sourceM := by
  unfold sourceM
  have h := Fintype.card_finset_len (α := Fin 1200) 600
  rw [Fintype.card_fin] at h
  exact (Fintype.card_congr vertexEquiv).trans h

def index (v : Vertex) : ℕ :=
  ((Fintype.orderIsoFinOfCardEq Vertex card_vertices).symm v).val + 1

lemma index_le (v : Vertex) : index v ≤ sourceM :=
  Nat.succ_le_of_lt ((Fintype.orderIsoFinOfCardEq Vertex card_vertices).symm v).isLt
lemma index_injective : Function.Injective index := by
  intro x y h
  apply (Fintype.orderIsoFinOfCardEq Vertex card_vertices).symm.injective
  apply Fin.ext
  exact Nat.add_right_cancel h

def graph : SimpleGraph Vertex where
  Adj i j := i ≠ j ∧ (i.val ∩ j.val).card < 200
  symm := ⟨by intro i j h; exact ⟨h.1.symm, by simpa only [Finset.inter_comm] using h.2⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

theorem no_triangle (a b c : Vertex) (hab : graph.Adj a b) (hbc : graph.Adj b c)
    (hca : graph.Adj c a) : False := by
  have hAB := Finset.card_union_add_card_inter a.val b.val
  have hABC := Finset.card_union_add_card_inter (a.val ∪ b.val) c.val
  have hI : ((a.val ∪ b.val) ∩ c.val).card ≤
      (a.val ∩ c.val).card + (b.val ∩ c.val).card := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_le _ _
  have hU : (a.val ∪ b.val ∪ c.val).card ≤ 1200 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (a.val ∪ b.val ∪ c.val))
  have ha := a.property
  have hb := b.property
  have hc := c.property
  have h₁ := hab.2
  have h₂ := hbc.2
  have h₃ : (a.val ∩ c.val).card < 200 := by simpa only [Finset.inter_comm] using hca.2
  omega

abbrev Edge := GraphEdges.Edge graph
abbrev Inc := GraphEdges.Inc graph
abbrev neighbor := GraphEdges.neighbor graph

lemma incidence_girth : 8 ≤ (Planar.incidenceGraph Inc).egirth :=
  GraphEdges.incidence_girth graph no_triangle

end
end OddKaplansky.SourceGraph

end

end OAI
end

section
namespace OAI

section
noncomputable section
open scoped Classical
namespace OddKaplansky

abbrev LocalGroup (p M : ℕ) :=
  RegularWreathProduct (Multiplicative (ZMod M)) (Multiplicative (Fin 3 → ZMod p))

namespace LocalGroup
variable (p M : ℕ)
abbrev Point := Fin 3 → ZMod p

instance [NeZero p] [NeZero M] : Fintype (LocalGroup p M) :=
  Fintype.ofFinite _

def u : Multiplicative (Point p) →* LocalGroup p M := RegularWreathProduct.inl

def c : LocalGroup p M :=
  ⟨fun x => Multiplicative.ofAdd (if x.toAdd = 0 then 1 else 0), 1⟩

def v : Multiplicative (Point p) →* LocalGroup p M :=
  (MulAut.conj (c p M)).toMonoidHom.comp (u p M)

lemma u_injective : Function.Injective (u p M) := by
  intro x y h
  exact congrArg RegularWreathProduct.right h

lemma v_injective : Function.Injective (v p M) :=
  (MulAut.conj (c p M)).injective.comp (u_injective p M)

@[simp] lemma u_right (x : Multiplicative (Point p)) :
    (u p M x).right = x := rfl
@[simp] lemma v_right (x : Multiplicative (Point p)) :
    (v p M x).right = x := by
  simp only [v, c, toAdd_eq_zero, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, MulAut.conj_apply, RegularWreathProduct.mul_right, u_right, one_mul, RegularWreathProduct.inv_right, inv_one, mul_one]

def direction (j : ZMod p) : Point p := ![1, j, j^2]

def line (j : ZMod p) : ZMod p →+ Point p where
  toFun a := a • direction p j
  map_zero' := zero_smul _ _
  map_add' _ _ := add_smul _ _ _

lemma line_injective (j : ZMod p) : Function.Injective (line p j) := by
  intro a b h
  have hh := congrFun h 0
  simpa only [line, direction, Matrix.smul_cons, smul_eq_mul, mul_one, Matrix.smul_empty, Fin.isValue, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.cons_val_zero] using hh

def edgeHom (outgoing : Bool) (j : ZMod p) :
    Multiplicative (ZMod p) →* LocalGroup p M :=
  (if outgoing then v p M else u p M).comp (line p j).toMultiplicative

lemma edgeHom_injective (outgoing : Bool) (j : ZMod p) :
    Function.Injective (edgeHom p M outgoing j) := by
  have hline : Function.Injective (line p j).toMultiplicative := line_injective p j
  cases outgoing with
  | false => exact (u_injective p M).comp hline
  | true => exact (v_injective p M).comp hline

@[simp] lemma edgeHom_right (outgoing : Bool) (j : ZMod p)
    (a : Multiplicative (ZMod p)) :
    (edgeHom p M outgoing j a).right = Multiplicative.ofAdd (line p j a.toAdd) := by
  cases outgoing <;> simp only [edgeHom, Bool.false_eq_true, ↓reduceIte, MonoidHom.coe_comp, AddMonoidHom.coe_toMultiplicative, Function.comp_apply, u_right, v_right]

section Independence
variable [Fact p.Prime]

lemma two_directions {x y a b : ZMod p} (hxy : x ≠ y)
    (h : line p x a + line p y b = 0) : a = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [line, direction, Matrix.smul_cons, smul_eq_mul, mul_one, Matrix.smul_empty, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.isValue, Pi.add_apply, Matrix.cons_val_zero, Pi.zero_apply, Matrix.cons_val_one] at h0 h1
  have hz : a * (x-y) = 0 := by linear_combination h1 - y * h0
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hxy)

lemma three_directions {x y z a b c : ZMod p} (hxy : x ≠ y) (hxz : x ≠ z)
    (h : line p x a + line p y b + line p z c = 0) : a = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [line, direction, Matrix.smul_cons, smul_eq_mul, mul_one, Matrix.smul_empty, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.add_cons, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_add_empty, Fin.isValue, Pi.add_apply, Matrix.cons_val_zero, Pi.zero_apply, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2
  have hz : a * ((x-y)*(x-z)) = 0 := by
    linear_combination h2 - (y+z) * h1 + y*z * h0
  exact (mul_eq_zero.mp hz).resolve_right
    (mul_ne_zero (sub_ne_zero.mpr hxy) (sub_ne_zero.mpr hxz))

lemma edge_word_one (o : Bool) (j : ZMod p) (a : Multiplicative (ZMod p))
    (ha : a ≠ 1) : edgeHom p M o j a ≠ 1 := by
  intro h
  exact ha (edgeHom_injective p M o j (h.trans (map_one _).symm))

lemma edge_word_two (o₁ o₂ : Bool) (j₁ j₂ : ZMod p)
    (a₁ a₂ : Multiplicative (ZMod p)) (ha : a₁ ≠ 1) (hj : j₁ ≠ j₂) :
    edgeHom p M o₁ j₁ a₁ * edgeHom p M o₂ j₂ a₂ ≠ 1 := by
  intro h
  have hr := congrArg (fun q : LocalGroup p M => q.right.toAdd) h
  simp only [RegularWreathProduct.mul_right, edgeHom_right, RegularWreathProduct.one_right] at hr
  change line p j₁ a₁.toAdd + line p j₂ a₂.toAdd = 0 at hr
  exact ha (congrArg Multiplicative.ofAdd (two_directions p hj hr))

lemma edge_word_three (o₁ o₂ o₃ : Bool) (j₁ j₂ j₃ : ZMod p)
    (a₁ a₂ a₃ : Multiplicative (ZMod p)) (ha : a₁ ≠ 1)
    (h₁₂ : j₁ ≠ j₂) (h₁₃ : j₁ ≠ j₃) :
    edgeHom p M o₁ j₁ a₁ * edgeHom p M o₂ j₂ a₂ * edgeHom p M o₃ j₃ a₃ ≠ 1 := by
  intro h
  have hr := congrArg (fun q : LocalGroup p M => q.right.toAdd) h
  simp only [RegularWreathProduct.mul_right, edgeHom_right, RegularWreathProduct.one_right] at hr
  change line p j₁ a₁.toAdd + line p j₂ a₂.toAdd + line p j₃ a₃.toAdd = 0 at hr
  exact ha (congrArg Multiplicative.ofAdd (three_directions p h₁₂ h₁₃ hr))

end Independence
end LocalGroup
end OddKaplansky

end
end

end OAI
end

section
namespace OAI

section

namespace OddKaplansky.SourceGluing
noncomputable section
open scoped Classical
open SourceGraph

def pDefinition : ℕ := sourcePrime
opaque pWrapped : Subtype (Eq pDefinition) := ⟨_, rfl⟩

def p : ℕ := pWrapped.1
theorem p_def : p = sourcePrime := by
  delta p
  rw [show pWrapped = ⟨pDefinition, rfl⟩ from Subtype.ext pWrapped.2.symm]
  rfl
attribute [irreducible] p pDefinition
attribute [eqns p_def] p
lemma p_prime : p.Prime := by rw [p_def]; exact sourcePrime_prime
lemma p_gt : sourceM < p := by rw [p_def]; exact sourcePrime_gt

instance : Fact p.Prime := ⟨p_prime⟩
instance : NeZero p := ⟨p_prime.ne_zero⟩
@[irreducible] noncomputable def modulus : ℕ := p ^ 4 - 1
lemma modulus_gt : 1 < modulus := by
  have hp : 3 ≤ p := by have := p_gt; have := sourceM_large; omega
  have h : 81 ≤ p ^ 4 := Nat.pow_le_pow_left hp 4
  unfold modulus
  omega
instance : NeZero modulus := ⟨by have := modulus_gt; omega⟩
abbrev H := LocalGroup p modulus

def edgeHom (v : Vertex) (e : Edge) : Multiplicative (ZMod p) →* H :=
  LocalGroup.edgeHom p modulus (decide (v = e.val.1)) (index (neighbor v e))

lemma neighbor_cast_injective (v : Vertex) : Function.Injective (fun e : {e : Edge // Inc v e} =>
    (index (neighbor v e.val) : ZMod p)) := by
  intro e f hef
  apply GraphEdges.neighbor_injective graph v
  apply index_injective
  have h₁ : index (neighbor v e.val) < p := (index_le _).trans_lt p_gt
  have h₂ : index (neighbor v f.val) < p := (index_le _).trans_lt p_gt
  have hh := congrArg ZMod.val hef
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] using hh

lemma shortWords : Planar.ShortWords Inc edgeHom where
  one v f _ a ha := LocalGroup.edge_word_one _ _ _ _ _ ha
  two v f g hf hg hfg a b ha _ := by
    apply LocalGroup.edge_word_two _ _ _ _ _ _ _ _ ha
    intro h
    exact hfg (congrArg Subtype.val (neighbor_cast_injective v (a₁ := ⟨f,hf⟩) (a₂ := ⟨g,hg⟩) h))
  three v f g h hf hg hh hfg _ hhf a b c ha _ _ := by
    have h₁ : (index (neighbor v f) : ZMod p) ≠ index (neighbor v g) := by
      intro he
      exact hfg (congrArg Subtype.val (neighbor_cast_injective v (a₁ := ⟨f,hf⟩)
        (a₂ := ⟨g,hg⟩) he))
    have h₂ : (index (neighbor v f) : ZMod p) ≠ index (neighbor v h) := by
      intro he
      exact hhf (congrArg Subtype.val (neighbor_cast_injective v (a₁ := ⟨f,hf⟩)
        (a₂ := ⟨h,hh⟩) he)).symm
    exact LocalGroup.edge_word_three _ _ _ _ _ _ _ _ _ _ _ ha h₁ h₂

abbrev G₀ := Gluing.Q Inc edgeHom
def vertex (v : Vertex) : H →* G₀ := Gluing.vertex Inc edgeHom v
lemma vertex_injective (v : Vertex) : Function.Injective (vertex v) :=
  Gluing.vertex_injective Inc edgeHom (GraphEdges.incident_exists graph) shortWords incidence_girth v

instance : Group.FG G₀ := inferInstance

end
end OddKaplansky.SourceGluing

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.BooleanPolynomial
noncomputable section
open scoped Classical BigOperators
open MvPolynomial
variable {σ : Type portUniverse1} {K : Type portUniverse2} [sectionInstance4 : Fintype σ] [sectionInstance5 : DecidableEq σ] [CommRing K]

def value (S : Finset σ) (i : σ) : K := if i ∈ S then 1 else 0

def coefficient (f : MvPolynomial σ K) (T : Finset σ) : K :=
  ∑ d ∈ f.support, if d.support = T then f.coeff d else 0

lemma support_card_le
    {σ : Type contextUniverse1}
    {K : Type contextUniverse2}
    [Fintype.{contextUniverse1} σ]
    [DecidableEq.{contextUniverse1 + 1} σ]
    [CommRing.{contextUniverse2} K] {f : MvPolynomial σ K} {d : σ →₀ ℕ} (hd : d ∈ f.support) :
    d.support.card ≤ f.totalDegree := by
  apply le_trans _ (le_totalDegree hd)
  change d.support.card ≤ ∑ i ∈ d.support, d i
  calc
    d.support.card = ∑ _i ∈ d.support, (1 : ℕ) := by simp only [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ _ := Finset.sum_le_sum (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

lemma bool_power_product
    {σ : Type contextUniverse1}
    {K : Type contextUniverse2}
    [Fintype.{contextUniverse1} σ]
    [DecidableEq.{contextUniverse1 + 1} σ]
    [CommRing.{contextUniverse2} K] (S : Finset σ) (d : σ →₀ ℕ) :
    d.prod (fun i e => value (K := K) S i ^ e) = if d.support ⊆ S then 1 else 0 := by
  change (∏ i ∈ d.support, value S i ^ d i) = _
  by_cases hs : d.support ⊆ S
  · rw [if_pos hs]
    exact Finset.prod_eq_one (fun i hi => by simp only [value, hs hi, ↓reduceIte, one_pow])
  · rw [if_neg hs]
    obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp hs
    apply Finset.prod_eq_zero hi
    simp only [value, hni, ↓reduceIte, ne_eq, Finsupp.mem_support_iff.mp hi, not_false_eq_true, zero_pow]

lemma evaluate (f : MvPolynomial σ K) (S : Finset σ) (n : ℕ) [Fintype {T : Finset σ // T.card ≤ n}] (hf : f.totalDegree ≤ n) :
    eval (value S) f = ∑ T : {T : Finset σ // T.card ≤ n},
      (if T.val ⊆ S then (1 : K) else 0) * coefficient f T.val := by
  rw [eval_eq]
  change (∑ d ∈ f.support, f.coeff d * d.prod (fun i e => value S i ^ e)) = _
  simp_rw [bool_power_product, coefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hdc : d.support.card ≤ n := (support_card_le hd).trans hf
  let T : {T : Finset σ // T.card ≤ n} := ⟨d.support, hdc⟩
  rw [Finset.sum_eq_single T]
  · simp only [mul_ite, mul_one, mul_zero, ↓reduceIte, mul_comm, T]
  · intro U _ hUT
    have hne : d.support ≠ U.val := by
      intro h
      apply hUT
      exact Subtype.ext h.symm
    simp only [hne, ↓reduceIte, mul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, mul_ite, ite_mul, one_mul, zero_mul, mul_zero, ite_eq_right_iff, IsEmpty.forall_iff]

end
end OddKaplansky.BooleanPolynomial

namespace OddKaplansky.GraphPolynomial
noncomputable section
open scoped Classical BigOperators
open MvPolynomial
variable {σ : Type portUniverse3} {K : Type portUniverse4} [sectionInstance6 : Fintype σ] [sectionInstance7 : DecidableEq σ] [Field K]

def factor (S : Finset σ) (r k : ℕ) : MvPolynomial σ K :=
  C ((r - k : ℕ) : K)⁻¹ * ((∑ i ∈ S, X i) + C (-(k : K)))

def polynomial (S : Finset σ) (r lo hi : ℕ) : MvPolynomial σ K :=
  ∏ k ∈ Finset.Ico lo hi, factor S r k

lemma degree_factor
    {σ : Type contextUniverse1}
    {K : Type contextUniverse2}
    [Fintype.{contextUniverse1} σ]
    [DecidableEq.{contextUniverse1 + 1} σ]
    [Field.{contextUniverse2} K] (S : Finset σ) (r k : ℕ) : (factor (K := K) S r k).totalDegree ≤ 1 := by
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact totalDegree_finsetSum_le (fun i _ => (totalDegree_X i).le)
  · rw [totalDegree_C]
    omega

lemma degree_polynomial (S : Finset σ) (r lo hi : ℕ) :
    (polynomial (K := K) S r lo hi).totalDegree ≤ hi - lo := by
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _k ∈ Finset.Ico lo hi, (1 : ℕ) := Finset.sum_le_sum (fun k _ => degree_factor S r k)
    _ = _ := by simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one]

lemma eval_variables
    {σ : Type contextUniverse1}
    {K : Type contextUniverse2}
    [Fintype.{contextUniverse1} σ]
    [DecidableEq.{contextUniverse1 + 1} σ]
    [Field.{contextUniverse2} K] (S T : Finset σ) :
    eval (BooleanPolynomial.value (K := K) T) (∑ i ∈ S, X i) = ((S ∩ T).card : K) := by
  simp only [eval_sum, eval_X, BooleanPolynomial.value]
  rw [Finset.sum_boole]
  congr 1

lemma eval_polynomial (S T : Finset σ) (r lo hi : ℕ) :
    eval (BooleanPolynomial.value (K := K) T) (polynomial S r lo hi) =
      ∏ k ∈ Finset.Ico lo hi, (((S ∩ T).card : K) - (k : K)) / ((r-k : ℕ) : K) := by
  simp only [polynomial, map_prod, factor, eval_mul, eval_add, eval_C, eval_variables,
    sub_eq_add_neg, div_eq_mul_inv, mul_comm]

lemma diagonal (S : Finset σ) (r lo hi : ℕ) (hS : S.card = r) (hhi : hi ≤ r)
    (hden : ∀ k ∈ Finset.Ico lo hi, ((r-k : ℕ) : K) ≠ 0) :
    eval (BooleanPolynomial.value (K := K) S) (polynomial S r lo hi) = 1 := by
  rw [eval_polynomial]
  apply Finset.prod_eq_one
  intro k hk
  have hk' : k ≤ r := Nat.le_of_lt ((Finset.mem_Ico.mp hk).2.trans_le hhi)
  simp only [Finset.inter_self, hS, ← Nat.cast_sub hk']
  exact div_self (hden k hk)

lemma vanishes (S T : Finset σ) (r lo hi : ℕ)
    (ha : lo ≤ (S ∩ T).card) (hb : (S ∩ T).card < hi) :
    eval (BooleanPolynomial.value (K := K) T) (polynomial S r lo hi) = 0 := by
  rw [eval_polynomial]
  apply Finset.prod_eq_zero (Finset.mem_Ico.mpr ⟨ha,hb⟩)
  simp only [sub_self, zero_div]

end
end OddKaplansky.GraphPolynomial

end

end OAI
end

section
namespace OAI


section
noncomputable section
open scoped Classical BigOperators
namespace OddKaplansky.GraphNumerics

def binomDefinition (k : ℕ) : ℕ := Nat.choose 1200 k
opaque binomWrapped : Subtype (Eq binomDefinition) := ⟨_, rfl⟩

def binom : (k : ℕ) → ℕ := binomWrapped.1
theorem binom_def (k : ℕ) : binom k = Nat.choose 1200 k := by
  delta binom
  rw [show binomWrapped = ⟨binomDefinition, rfl⟩ from Subtype.ext binomWrapped.2.symm]
  rfl
attribute [irreducible] binom binomDefinition
attribute [eqns binom_def] binom

lemma choose_mono_small {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 600) :
    binom a ≤ binom b := by
  induction hab with
  | refl => exact le_rfl
  | @step b hab ih =>
    apply (ih (by omega)).trans
    rw [binom_def, binom_def]
    apply Nat.choose_le_succ_of_lt_half_left
    omega

lemma choose_step (k : ℕ) (hk : k ≤ 499) :
    7 * binom k ≤ 5 * binom (k+1) := by
  have he := Nat.choose_succ_right_eq 1200 k
  rw [← binom_def (k+1), ← binom_def k] at he
  have hc : 7 * (k+1) ≤ 5 * (1200-k) := by omega
  have hh := Nat.mul_le_mul_left (binom k) hc
  apply Nat.le_of_mul_le_mul_right (c := k+1)
  · calc 7 * binom k * (k+1) = binom k * (7*(k+1)) := by ring
      _ ≤ binom k * (5*(1200-k)) := hh
      _ = 5 * (binom k * (1200-k)) := by ring
      _ = 5 * binom (k+1) * (k+1) := by rw [← he]; ring
  · omega

lemma choose_growth (n : ℕ) (hn : n ≤ 100) :
    7^n * binom 400 ≤ 5^n * binom (400+n) := by
  induction n with
  | zero => simp only [pow_zero, one_mul, add_zero, Std.le_refl]
  | succ n ih =>
    have hi := ih (by omega)
    have hs := choose_step (400+n) (by omega)
    calc
      _ = 7 * (7^n * binom 400) := by ring
      _ ≤ 7 * (5^n * binom (400+n)) := Nat.mul_le_mul_left _ hi
      _ = 5^n * (7 * binom (400+n)) := by ring
      _ ≤ 5^n * (5 * binom (400+n+1)) := Nat.mul_le_mul_left _ hs
      _ = _ := by simp only [pow_succ, Nat.add_assoc]; ring

lemma sum_small_bound : (∑ j ∈ Finset.range 401, binom j) ≤ 401 * binom 400 := by
  calc
    _ ≤ ∑ _j ∈ Finset.range 401, binom 400 :=
      Finset.sum_le_sum (fun j hj => choose_mono_small (by have := Finset.mem_range.mp hj; omega) (by omega))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]

lemma ratio_bound : 100 * (∑ j ∈ Finset.range 401, binom j) < binom 600 := by
  have hg := choose_growth 100 (by omega)
  have hm := choose_mono_small (a := 500) (b := 600) (by omega) (by omega)
  have hp : 0 < binom 400 := by rw [binom_def]; exact Nat.choose_pos (by omega)
  have hc : 40100 * 5^100 < 7^100 := by norm_num
  have hsmall := sum_small_bound
  have ht := Nat.mul_le_mul_left (5^100) (Nat.mul_le_mul_left 100 hsmall)
  have hstrict := Nat.mul_lt_mul_of_pos_right hc hp
  have hlast := Nat.mul_le_mul_left (5^100) hm
  apply Nat.lt_of_mul_lt_mul_left (a := 5^100)
  calc _ ≤ 5^100*(100*(401*binom 400)) := ht
    _ = 40100*5^100*binom 400 := by ring
    _ < 7^100*binom 400 := hstrict
    _ ≤ 5^100*binom (400+100) := hg
    _ ≤ 5^100*binom 600 := hlast

lemma source_ratio_bound :
    100 * (∑ j ∈ Finset.range 401, Nat.choose 1200 j) < Nat.choose 1200 600 := by
  simpa only [binom_def] using ratio_bound

variable (E : Type portUniverse1) [Fintype E]
def smallSetEquiv (n : ℕ) :
    {T : Finset E // T.card ≤ n} ≃ (Σ k : Fin (n+1), {T : Finset E // T.card = k.val}) where
  toFun T := ⟨⟨T.val.card, by omega⟩, ⟨T.val,rfl⟩⟩
  invFun v := ⟨v.2.val, by have := v.1.isLt; rw [v.2.property]; omega⟩
  left_inv _ := rfl
  right_inv v := by
    rcases v with ⟨⟨k,hk⟩,⟨T,hT⟩⟩
    change T.card = k at hT
    dsimp
    subst k
    rfl

lemma card_small_sets (n : ℕ) :
    Fintype.card {T : Finset E // T.card ≤ n} = ∑ j ∈ Finset.range (n+1), Nat.choose (Fintype.card E) j := by
  rw [Fintype.card_congr (smallSetEquiv E n), Fintype.card_sigma]
  simp only [Fintype.card_finset_len]
  exact Fin.sum_univ_eq_sum_range _ _

end OddKaplansky.GraphNumerics

end
end

end OAI
end

section
namespace OAI



section

namespace OddKaplansky.SourceFit
noncomputable section
open scoped Classical BigOperators
open SourceGraph
variable {K : Type portUniverse1} [Field K]
variable (p : ℕ) [sectionInstance8 : Fact p.Prime] [CharP K p] (hp : 1200 < p)

abbrev Slot := {T : Finset (Fin 1200) // T.card ≤ 400}
def polynomial (j : Vertex) : MvPolynomial (Fin 1200) K :=
  GraphPolynomial.polynomial j.val 600 200 600

def alpha (i : Vertex) (T : Slot) : K := if T.val ⊆ i.val then 1 else 0
def beta (j : Vertex) (T : Slot) : K := BooleanPolynomial.coefficient (polynomial j) T.val

def fitting (i j : Vertex) : K := ∑ T : Slot, alpha i T * beta j T

lemma denominator
    {K : Type contextUniverse1}
    [contextInstance1 : Field.{contextUniverse1} K]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance1))))
  p]
    (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1200) (instOfNatNat (nat_lit 1200))) p) (k : ℕ) (hk : k ∈ Finset.Ico 200 600) : ((600-k : ℕ) : K) ≠ 0 := by
  have hk₁ : 0 < 600-k := by have := Finset.mem_Ico.mp hk; omega
  have hk₂ : 600-k < p := by omega
  exact (CharP.cast_eq_zero_iff K p (600-k)).not.mpr (Nat.not_dvd_of_pos_of_lt hk₁ hk₂)

include hp in
lemma fitting_diagonal (i : Vertex) : fitting (K := K) i i = 1 := by
  have hdeg : (polynomial (K := K) i).totalDegree ≤ 400 := GraphPolynomial.degree_polynomial _ _ _ _
  simp only [fitting, alpha, beta]
  trans MvPolynomial.eval (BooleanPolynomial.value i.val) (polynomial (K := K) i)
  · exact (BooleanPolynomial.evaluate (polynomial i) i.val 400 hdeg).symm
  exact GraphPolynomial.diagonal i.val 600 200 600 i.property (by omega) (denominator p hp)

lemma intersection_lt (i j : Vertex) (hij : i ≠ j) : (i.val ∩ j.val).card < 600 := by
  have hle : (i.val ∩ j.val).card ≤ 600 := by
    rw [← i.property]
    exact Finset.card_le_card Finset.inter_subset_left
  by_contra hn
  have hecard : (i.val ∩ j.val).card = i.val.card := by rw [i.property]; omega
  have he : i.val ∩ j.val = i.val := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hecard.ge
  have hij' : i.val ⊆ j.val := by rw [← he]; exact Finset.inter_subset_right
  exact hij (Vertex.ext (Finset.eq_of_subset_of_card_le hij' (by rw [i.property,j.property])))

lemma fitting_nonedge (i j : Vertex) (hij : i ≠ j) (hn : ¬ graph.Adj i j) :
    fitting (K := K) i j = 0 := by
  have hlo : 200 ≤ (j.val ∩ i.val).card := by
    rw [Finset.inter_comm]
    by_contra hh
    apply hn
    exact ⟨hij,by omega⟩
  have hhi : (j.val ∩ i.val).card < 600 := intersection_lt j i hij.symm
  have hdeg : (polynomial (K := K) j).totalDegree ≤ 400 := GraphPolynomial.degree_polynomial _ _ _ _
  simp only [fitting, alpha, beta]
  trans MvPolynomial.eval (BooleanPolynomial.value i.val) (polynomial (K := K) j)
  · exact (BooleanPolynomial.evaluate (polynomial j) i.val 400 hdeg).symm
  exact GraphPolynomial.vanishes j.val i.val 600 200 600 hlo hhi

lemma card_slots : Fintype.card Slot = ∑ k ∈ Finset.range 401, Nat.choose 1200 k := by
  have he := GraphNumerics.card_small_sets (Fin 1200) 400
  simpa only [Fintype.card_fin] using he

lemma ratio_bound : 100 * Fintype.card Slot < sourceM := by
  rw [card_slots]
  unfold sourceM
  exact GraphNumerics.source_ratio_bound

end
end OddKaplansky.SourceFit

end

end OAI
end

section
namespace OAI


section
noncomputable section
open scoped Classical BigOperators
namespace OddKaplansky.CharacterIdempotents
variable {K : Type portUniverse1} {A : Type portUniverse2} {G : Type portUniverse3} [Field K] [Group A] [Fintype A] [Group G]

def projector (χ : A →* Kˣ) : MonoidAlgebra K A :=
  (Fintype.card A : K)⁻¹ • ∑ a : A, MonoidAlgebra.single a ((χ a : K)⁻¹)

lemma sum_character_eq_zero (χ : A →* Kˣ) (hχ : χ ≠ 1) :
    ∑ a : A, (χ a : K) = 0 := by
  have hn : ∃ b : A, (χ b : K) ≠ 1 := by
    by_contra! h
    apply hχ
    ext b
    exact h b
  obtain ⟨b, hb⟩ := hn
  have hh : (χ b : K) * ∑ a : A, (χ a : K) = ∑ a : A, (χ a : K) := by
    rw [Finset.mul_sum]
    simp only [← Units.val_mul, ← map_mul]
    exact Equiv.sum_comp (Equiv.mulLeft b) (fun a => (χ a : K))
  by_contra hs
  exact hb ((mul_eq_right₀ hs).mp hh)

lemma projector_mul_single (χ : A →* Kˣ) (b : A) :
    projector χ * MonoidAlgebra.single b 1 = (χ b : K) • projector χ := by
  unfold projector
  rw [smul_mul_assoc, Finset.sum_mul, smul_smul]
  rw [mul_comm (χ b : K), ← smul_smul]
  congr 1
  rw [Finset.smul_sum]
  calc
    (∑ a : A, MonoidAlgebra.single a ((χ a : K)⁻¹) * MonoidAlgebra.single b 1) =
        ∑ a : A, (χ b : K) • MonoidAlgebra.single (a * b) ((χ (a * b) : K)⁻¹) := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [MonoidAlgebra.single_mul_single, mul_comm, one_mul, map_mul, Units.val_mul, mul_inv_rev, MonoidAlgebra.smul_single, smul_eq_mul, ne_eq, Units.ne_zero, not_false_eq_true, mul_inv_cancel_left₀]
    _ = _ := Equiv.sum_comp (Equiv.mulRight b)
      (fun a : A => (χ b : K) • MonoidAlgebra.single a ((χ a : K)⁻¹))

lemma projector_mul (χ ψ : A →* Kˣ) :
    projector χ * projector ψ =
      ((Fintype.card A : K)⁻¹ * ∑ b : A, ((χ b : K) * (ψ b : K)⁻¹)) •
        projector χ := by
  conv_lhs => rhs; unfold projector
  rw [mul_smul_comm, Finset.mul_sum]
  have hh (b : A) : projector χ * MonoidAlgebra.single b ((ψ b : K)⁻¹) =
      ((χ b : K) * (ψ b : K)⁻¹) • projector χ := by
    rw [show MonoidAlgebra.single b ((ψ b : K)⁻¹) =
      (ψ b : K)⁻¹ • MonoidAlgebra.single b 1 by simp only [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]]
    rw [mul_smul_comm, projector_mul_single, smul_smul, mul_comm]
  simp_rw [hh]
  rw [← Finset.sum_smul, smul_smul]

lemma projector_idempotent (χ : A →* Kˣ) (hcard : (Fintype.card A : K) ≠ 0) :
    IsIdempotentElem (projector χ) := by
  change projector χ * projector χ = projector χ
  rw [projector_mul]
  simp only [ne_eq, Units.ne_zero, not_false_eq_true, mul_inv_cancel₀, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard, inv_mul_cancel₀, one_smul]

lemma projector_orthogonal (χ ψ : A →* Kˣ) (hne : χ ≠ ψ) :
    projector χ * projector ψ = 0 := by
  rw [projector_mul]
  have hn : χ * ψ⁻¹ ≠ 1 := by
    intro h
    apply hne
    apply MonoidHom.ext
    intro a
    have hh := congrArg (fun f : A →* Kˣ => f a) h
    exact mul_inv_eq_one.mp hh
  have h := sum_character_eq_zero (χ * ψ⁻¹) hn
  simpa only [smul_eq_zero, mul_eq_zero, inv_eq_zero, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, mul_zero, zero_smul] using congrArg (fun c : K => ((Fintype.card A : K)⁻¹ * c) • projector χ) h

lemma projector_one_coeff (χ : A →* Kˣ) :
    (projector χ).coeff 1 = (Fintype.card A : K)⁻¹ := by
  simp only [projector, MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.coe_smul, Finsupp.coe_finsetSum, Pi.smul_apply, Finset.sum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, map_one, Units.val_one, inv_one, smul_eq_mul, mul_one]

lemma projector_ne_zero (χ : A →* Kˣ) (hcard : (Fintype.card A : K) ≠ 0) :
    projector χ ≠ 0 := by
  intro h
  have := congrArg (fun p : MonoidAlgebra K A => p.coeff 1) h
  rw [projector_one_coeff] at this
  exact (inv_ne_zero hcard) this

def pushed (f : A →* G) (χ : A →* Kˣ) : MonoidAlgebra K G :=
  MonoidAlgebra.mapDomainAlgHom K K f (projector χ)

lemma pushed_eq_sum (f : A →* G) (χ : A →* Kˣ) :
    pushed f χ = (Fintype.card A : K)⁻¹ •
      ∑ a : A, MonoidAlgebra.single (f a) ((χ a : K)⁻¹) := by
  simp only [pushed, projector, map_smul, map_sum, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single]

lemma pushed_idempotent (f : A →* G) (χ : A →* Kˣ)
    (hc : (Fintype.card A : K) ≠ 0) :
    pushed f χ * pushed f χ = pushed f χ := by
  unfold pushed
  rw [← map_mul, projector_idempotent χ hc]

lemma pushed_orthogonal (f : A →* G) (χ ψ : A →* Kˣ) (hne : χ ≠ ψ) :
    pushed f χ * pushed f ψ = 0 := by
  unfold pushed
  rw [← map_mul, projector_orthogonal χ ψ hne, map_zero]

lemma pushed_ne_zero (f : A →* G) (hf : Function.Injective f) (χ : A →* Kˣ)
    (hc : (Fintype.card A : K) ≠ 0) : pushed f χ ≠ 0 := by
  intro h
  exact projector_ne_zero χ hc ((MonoidAlgebra.mapDomain_injective hf) (h.trans (MonoidAlgebra.mapDomain_zero f).symm))

lemma pushed_mul_single (f : A →* G) (χ : A →* Kˣ) (b : A) :
    pushed f χ * MonoidAlgebra.single (f b) 1 = (χ b : K) • pushed f χ := by
  have h := congrArg (MonoidAlgebra.mapDomainAlgHom K K f) (projector_mul_single χ b)
  rw [map_mul, map_smul] at h
  simpa only [pushed, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single] using h

lemma pushed_central (f : A →* G) (χ : A →* Kˣ)
    (hf : ∀ a g, Commute (f a) g) (x : MonoidAlgebra K G) :
    Commute (pushed f χ) x := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    change pushed f χ * MonoidAlgebra.single g 1 = _
    rw [pushed_eq_sum, smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one, one_mul,
      (hf a g).eq]
  | add x y hx hy => exact hx.add_right hy
  | smul r x hx => exact hx.smul_right r

end OddKaplansky.CharacterIdempotents

namespace OddKaplansky.Fourier
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse4} {E : Type portUniverse5} [Field K] [Fintype E] (M : ℕ) [NeZero M]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ M)

abbrev C := Multiplicative (ZMod M)
abbrev A := E → C M

def cyclicCharacter : C M →* Kˣ :=
  (AddChar.zmodChar M hζ.pow_eq_one).toMonoidHom.toHomUnits
lemma cyclicCharacter_injective : Function.Injective (cyclicCharacter M hζ) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  apply ZMod.val_injective M
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  exact congrArg (fun u : Kˣ => (u : K)) hab

def character (lmb : A (E := E) M) : A (E := E) M →* Kˣ :=
  (cyclicCharacter M hζ).comp (show A (E := E) M →* C M from
    { toFun := fun a => Multiplicative.ofAdd (∑ e, (lmb e).toAdd * (a e).toAdd)
      map_one' := by simp only [Pi.one_apply, toAdd_one, mul_zero, Finset.sum_const_zero, ofAdd_zero]
      map_mul' := by intro a b; simp only [Pi.mul_apply, toAdd_mul, mul_add, Finset.sum_add_distrib, ofAdd_add, ofAdd_sum] })

lemma character_apply (lmb a : A (E := E) M) :
    character M hζ lmb a = cyclicCharacter M hζ (Multiplicative.ofAdd
      (∑ e, (lmb e).toAdd * (a e).toAdd)) := rfl

lemma character_symm (lmb a : A (E := E) M) : character M hζ lmb a = character M hζ a lmb := by
  simp only [character_apply, mul_comm]

lemma character_mul (lmb μ : A (E := E) M) :
    character M hζ (lmb * μ) = character M hζ lmb * character M hζ μ := by
  apply MonoidHom.ext
  intro a
  simp only [MonoidHom.mul_apply, character_apply, Pi.mul_apply, toAdd_mul,
    add_mul, Finset.sum_add_distrib, ofAdd_add, map_mul]

lemma character_mulSingle (lmb : A (E := E) M) (i : E) :
    character M hζ lmb (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod M))) =
      cyclicCharacter M hζ (lmb i) := by
  rw [character_apply]
  have hs : (∑ e, (lmb e).toAdd *
      ((Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod M)) : A (E := E) M) e).toAdd) = (lmb i).toAdd := by
    simp only [Pi.mulSingle_apply, apply_ite, toAdd_ofAdd, toAdd_one, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [hs, ofAdd_toAdd]

lemma character_injective : Function.Injective (character (E := E) M hζ) := by
  intro lmb μ he
  funext i
  apply cyclicCharacter_injective M hζ
  have h := congrArg (fun χ : A (E := E) M →* Kˣ =>
    χ (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod M)))) he
  simpa only [character_mulSingle] using h

@[simp] lemma character_one : character (E := E) M hζ 1 = 1 := by
  ext a
  simp only [MonoidHom.toAdditiveRight_apply_apply, MonoidHom.coe_comp, MonoidHom.coe_mulSingle, Function.comp_apply, character_apply, Pi.one_apply, toAdd_one, zero_mul, Finset.sum_const_zero, ofAdd_zero, map_one, ofMul_one, toMul_zero, Units.val_one, MonoidHom.one_comp, MonoidHom.one_apply]

lemma character_ne_one (a : A (E := E) M) (ha : a ≠ 1) : character M hζ a ≠ 1 := by
  intro hh
  exact ha (character_injective M hζ (hh.trans (character_one M hζ).symm))

lemma sum_inverse_characters (a : A (E := E) M) (ha : a ≠ 1) :
    ∑ lmb : A (E := E) M, ((character M hζ lmb a : K)⁻¹) = 0 := by
  have hχ : (character M hζ a)⁻¹ ≠ 1 := by
    intro h
    apply character_ne_one M hζ a ha
    apply MonoidHom.ext
    intro b
    have hh := congrArg (fun χ : A (E := E) M →* Kˣ => (χ b)⁻¹) h
    simpa only [MonoidHom.one_apply, MonoidHom.inv_apply, inv_inv, inv_one] using hh
  simpa only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, character_symm] using
    CharacterIdempotents.sum_character_eq_zero ((character M hζ a)⁻¹) hχ

lemma sum_projector (hc : (Fintype.card (A (E := E) M) : K) ≠ 0) :
    ∑ lmb : A (E := E) M, CharacterIdempotents.projector (character M hζ lmb) = 1 := by
  have hp (lmb a : A (E := E) M) :
      (CharacterIdempotents.projector (character M hζ lmb)).coeff a =
        (Fintype.card (A (E := E) M) : K)⁻¹ * ((character M hζ lmb a : K)⁻¹) := by
    simp only [CharacterIdempotents.projector, Fintype.card_pi, Fintype.card_multiplicative, ZMod.card, Finset.prod_const, Finset.card_univ, Nat.cast_pow, MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.coe_smul, Finsupp.coe_finsetSum, Pi.smul_apply, Finset.sum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, smul_eq_mul]
  ext a
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply']
  simp_rw [hp]
  rw [← Finset.mul_sum]
  by_cases ha : a = 1
  · subst a
    simp only [map_one, Units.val_one, inv_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, MonoidAlgebra.coeff_one_one]
    exact inv_mul_cancel₀ hc
  · rw [sum_inverse_characters M hζ a ha]
    simp only [Fintype.card_pi, Fintype.card_multiplicative, ZMod.card, Finset.prod_const, Finset.card_univ, Nat.cast_pow, mul_zero, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, ne_eq, ha, not_false_eq_true, Finsupp.single_eq_of_ne]

end
end OddKaplansky.Fourier

end
end

end OAI
end

section
namespace OAI



section

namespace OddKaplansky.CharacterIdempotents
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {A : Type portUniverse2} {G : Type portUniverse3} [Field K] [Group A] [Fintype A] [Group G]
lemma pushed_conjugate (f : A →* G) (χ ψ : A →* Kˣ) (σ : A ≃* A) (g : G)
    (hg : ∀ a, g * f a * g⁻¹ = f (σ a)) (hχ : ∀ a, ψ (σ a) = χ a) :
    MonoidAlgebra.single g 1 * pushed f χ * MonoidAlgebra.single g⁻¹ 1 = pushed f ψ := by
  rw [pushed_eq_sum, pushed_eq_sum]
  simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  calc
    _ = ∑ a : A, MonoidAlgebra.single (f (σ a)) ((ψ (σ a) : K)⁻¹) := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [MonoidAlgebra.single_mul_single, one_mul, mul_one, hg, hχ]
    _ = _ := Equiv.sum_comp σ.toEquiv (fun a : A =>
      (MonoidAlgebra.single (f a) ((ψ a : K)⁻¹) : MonoidAlgebra K G))
end
end OddKaplansky.CharacterIdempotents

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse4} {H : Type portUniverse5} [Field K] [Group H] [sectionInstance9 : Fintype H]
variable (M : ℕ) [sectionInstance10 : NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
abbrev Base := H → Fourier.C M
abbrev Wreath := RegularWreathProduct (Fourier.C M) H

def shift (h : H) : Base (H := H) M ≃* Base (H := H) M where
  toFun a x := a (h⁻¹ * x)
  invFun a x := a (h * x)
  left_inv a := by funext x; simp only [inv_mul_cancel_left]
  right_inv a := by funext x; simp only [mul_inv_cancel_left]
  map_mul' _ _ := rfl
@[simp] lemma shift_apply
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (h : H) (a : Base (H := H) M) (x : H) : shift M h a x = a (h⁻¹*x) := rfl
@[simp] lemma shift_one
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] : shift (H := H) M 1 = MulEquiv.refl _ := by ext a x; simp only [shift_apply, inv_one, one_mul, MulEquiv.refl_apply]
@[simp] lemma shift_mul
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (h g : H) (a : Base (H := H) M) : shift M (h*g) a = shift M h (shift M g a) := by
  funext x
  simp only [shift_apply, mul_inv_rev, mul_assoc]
lemma character_shift (h : H) (lmb a : Base (H := H) M) :
    Fourier.character M hζ (shift M h lmb) (shift M h a) = Fourier.character M hζ lmb a := by
  simp only [Fourier.character_apply, shift_apply]
  congr 1
  apply congrArg Multiplicative.ofAdd
  exact Equiv.sum_comp (Equiv.mulLeft h⁻¹) (fun x : H => (lmb x).toAdd * (a x).toAdd)
def base : Base (H := H) M →* Wreath (H := H) M where
  toFun a := ⟨a,1⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp only [Pi.mul_apply, toAdd_mul, RegularWreathProduct.mul_left, inv_one, one_mul, RegularWreathProduct.mul_right, mul_one]
@[simp] lemma base_left
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (a : Base (H := H) M) : (base M a).left = a := rfl
@[simp] lemma base_right
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (a : Base (H := H) M) : (base M a).right = 1 := rfl
def top : H →* Wreath (H := H) M := RegularWreathProduct.inl
lemma top_conjugate
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (h : H) (a : Base (H := H) M) :
    top M h * base M a * (top M h)⁻¹ = base M (shift M h a) := by
  ext <;> simp only [top, base, MonoidHom.coe_mk, OneHom.coe_mk, RegularWreathProduct.mul_left, RegularWreathProduct.left_inl, RegularWreathProduct.right_inl, one_mul, RegularWreathProduct.mul_right, mul_one, RegularWreathProduct.inv_left, mul_inv_cancel_left, Pi.inv_apply, Pi.one_apply, inv_one, Pi.mul_apply, shift_apply, RegularWreathProduct.inv_right, mul_inv_cancel]
def projector (lmb : Base (H := H) M) : MonoidAlgebra K (Wreath (H := H) M) :=
  CharacterIdempotents.pushed (base M) (Fourier.character M hζ lmb)
def topElt (h : H) : MonoidAlgebra K (Wreath (H := H) M) := MonoidAlgebra.single (top M h) 1
lemma projector_idempotent (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0) (lmb : Base (H := H) M) :
    projector M hζ lmb * projector M hζ lmb = projector M hζ lmb :=
  CharacterIdempotents.pushed_idempotent _ _ hc
lemma projector_orthogonal (lmb μ : Base (H := H) M) (hne : lmb ≠ μ) :
    projector M hζ lmb * projector M hζ μ = 0 :=
  CharacterIdempotents.pushed_orthogonal _ _ _ (fun he => hne (Fourier.character_injective M hζ he))
lemma translated (h : H) (lmb : Base (H := H) M) :
    topElt M h * projector M hζ lmb * topElt M h⁻¹ = projector M hζ (shift M h lmb) := by
  simp only [topElt, map_inv]
  exact CharacterIdempotents.pushed_conjugate _ _ _ (shift M h) _ (top_conjugate M h)
    (character_shift M hζ h lmb)
lemma sum_projector (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0) :
    ∑ lmb : Base (H := H) M, projector M hζ lmb = 1 := by
  have he := congrArg (MonoidAlgebra.mapDomainAlgHom K K (base (H := H) M)) (Fourier.sum_projector M hζ hc)
  simpa only [map_sum, map_one, projector, CharacterIdempotents.pushed] using he
end
end OddKaplansky.WreathFourier

end

end OAI
end

section
namespace OAI



section

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {H : Type portUniverse2} [Field K] [Group H] [sectionInstance11 : Fintype H]
variable (M : ℕ) [sectionInstance12 : NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)

@[simp] lemma shift_inverse_shift
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (h : H) (a : Base (H := H) M) :
    shift M h⁻¹ (shift M h a) = a := by funext x; simp only [shift_apply, inv_inv, inv_mul_cancel_left]
@[simp] lemma shift_shift_inverse
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (h : H) (a : Base (H := H) M) :
    shift M h (shift M h⁻¹ a) = a := by funext x; simp only [shift_apply, inv_inv, mul_inv_cancel_left]

lemma character_shift_right (h : H) (lmb a : Base (H := H) M) :
    Fourier.character M hζ lmb (shift M h a) = Fourier.character M hζ (shift M h⁻¹ lmb) a := by
  have he := character_shift M hζ h (shift M h⁻¹ lmb) a
  simpa only [shift_shift_inverse] using he

def rhoGroup : Wreath (H := H) M →*
    Matrix (Base (H := H) M) (Base (H := H) M) (MonoidAlgebra K H) where
  toFun g := Matrix.of fun x y => if x = shift M g.right y then
    MonoidAlgebra.single g.right (Fourier.character M hζ x g.left : K) else 0
  map_one' := by
    apply Matrix.ext
    intro x y
    simp only [RegularWreathProduct.one_right, shift_one, MulEquiv.refl_apply, RegularWreathProduct.one_left, map_one, Units.val_one, Matrix.of_apply, Matrix.one_apply, MonoidAlgebra.one_def]
  map_mul' g k := by
    apply Matrix.ext
    intro x y
    rw [Matrix.mul_apply, Finset.sum_eq_single (shift M k.right y)]
    · simp only [Matrix.of_apply, RegularWreathProduct.mul_left,
        RegularWreathProduct.mul_right, shift_mul, ite_true]
      change (if x = shift M g.right (shift M k.right y) then
        MonoidAlgebra.single (g.right*k.right)
          (Fourier.character M hζ x (g.left * shift M g.right k.left) : K) else 0) = _
      by_cases he : x = shift M g.right (shift M k.right y)
      · rw [if_pos he, if_pos he, MonoidAlgebra.single_mul_single]
        congr 1
        rw [map_mul, Units.val_mul, character_shift_right, he, shift_inverse_shift]
      · simp only [he, ↓reduceIte, zero_mul]
    · intro z _ hzy
      simp only [Matrix.of_apply, hzy, ↓reduceIte, mul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, Matrix.of_apply, ↓reduceIte, ite_mul, MonoidAlgebra.single_mul_single, zero_mul, ite_eq_right_iff, MonoidAlgebra.single_eq_zero, mul_eq_zero, Units.ne_zero, or_self, imp_false, IsEmpty.forall_iff]

def rho : MonoidAlgebra K (Wreath (H := H) M) →ₐ[K]
    Matrix (Base (H := H) M) (Base (H := H) M) (MonoidAlgebra K H) :=
  MonoidAlgebra.lift K _ _ (rhoGroup M hζ)

lemma rho_single (g : Wreath (H := H) M) (c : K) (x y : Base (H := H) M) :
    rho M hζ (MonoidAlgebra.single g c) x y =
    if x = shift M g.right y then MonoidAlgebra.single g.right
      (c * (Fourier.character M hζ x g.left : K)) else 0 := by
  rw [rho, MonoidAlgebra.lift_single]
  change c • (if x = shift M g.right y then
    MonoidAlgebra.single g.right (Fourier.character M hζ x g.left : K) else 0) = _
  split_ifs <;> simp only [MonoidAlgebra.smul_single, smul_eq_mul, smul_zero]

lemma rho_top (h : H) (x y : Base (H := H) M) : rho M hζ (topElt M h) x y =
    if x = shift M h y then MonoidAlgebra.single h 1 else 0 := by
  rw [topElt, rho_single]
  simp only [top, RegularWreathProduct.right_inl, RegularWreathProduct.left_inl, map_one, Units.val_one, mul_one]

end
end OddKaplansky.WreathFourier

end

end OAI
end

section
namespace OAI


section

namespace OddKaplansky.CharacterIdempotents
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {A : Type portUniverse2} [Field K] [Group A] [Fintype A]
lemma character_pairing (χ ψ : A →* Kˣ) :
    (∑ a : A, (χ a : K) * (ψ a : K)⁻¹) = if χ = ψ then (Fintype.card A : K) else 0 := by
  by_cases he : χ = ψ
  · subst ψ; simp only [ne_eq, Units.ne_zero, not_false_eq_true, mul_inv_cancel₀, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ↓reduceIte]
  · rw [if_neg he]
    have hn : χ * ψ⁻¹ ≠ 1 := by
      intro h
      apply he
      apply MonoidHom.ext
      intro a
      exact mul_inv_eq_one.mp (congrArg (fun f : A →* Kˣ => f a) h)
    simpa only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val] using sum_character_eq_zero (χ * ψ⁻¹) hn

end
end OddKaplansky.CharacterIdempotents

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse3} {H : Type portUniverse4} [Field K] [Group H] [Fintype H]
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)

lemma rho_projector (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
    (lmb x y : Base (H := H) M) :
    rho M hζ (projector M hζ lmb) x y = if x = y ∧ x = lmb then 1 else 0 := by
  unfold projector
  rw [CharacterIdempotents.pushed_eq_sum, map_smul, map_sum]
  simp only [Matrix.smul_apply, Matrix.sum_apply, rho_single, base_left, base_right, shift_one,
    MulEquiv.refl_apply]
  by_cases hxy : x = y
  · subst y
    simp only [ite_true,       true_and]
    have hs (f : Base (H := H) M → K) : (∑ a, MonoidAlgebra.single (1 : H) (f a)) =
        MonoidAlgebra.single 1 (∑ a, f a) :=
      (map_sum (MonoidAlgebra.singleAddHom (1 : H)) f Finset.univ).symm
    rw [hs]
    have he := CharacterIdempotents.character_pairing
      (Fourier.character M hζ x) (Fourier.character M hζ lmb)
    have hi : Fourier.character M hζ x = Fourier.character M hζ lmb ↔ x = lmb :=
      (Fourier.character_injective M hζ).eq_iff
    simp only [hi] at he
    simp_rw [mul_comm ((Fourier.character M hζ lmb _ : K)⁻¹)]
    rw [he]
    split_ifs
    · rw [MonoidAlgebra.smul_single, smul_eq_mul]
      change MonoidAlgebra.single (1 : H) ((Fintype.card (Base (H := H) M) : K)⁻¹ *
        (Fintype.card (Base (H := H) M) : K)) = MonoidAlgebra.single 1 1
      rw [inv_mul_cancel₀ hc]
    · simp only [Fintype.card_pi, Fintype.card_multiplicative, ZMod.card, Finset.prod_const, Finset.card_univ, Nat.cast_pow, MonoidAlgebra.single_zero, smul_zero]
  · simp only [Fintype.card_pi, Fintype.card_multiplicative, ZMod.card, Finset.prod_const, Finset.card_univ, Nat.cast_pow, hxy, ↓reduceIte, Finset.sum_const_zero, smul_zero, false_and]

def normal (lmb : Base (H := H) M) (h : H) : MonoidAlgebra K (Wreath (H := H) M) :=
  projector M hζ lmb * topElt M h

lemma rho_normal (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
    (lmb : Base (H := H) M) (h : H) (x y : Base (H := H) M) :
    rho M hζ (normal M hζ lmb h) x y =
      if x = lmb ∧ x = shift M h y then MonoidAlgebra.single h 1 else 0 := by
  rw [normal, map_mul, Matrix.mul_apply, Finset.sum_eq_single x]
  · rw [rho_projector M hζ hc, rho_top]
    by_cases hxl : x = lmb <;> by_cases hxy : x = shift M h y <;> simp only [hxl, and_self, ↓reduceIte, mul_ite, one_mul, mul_zero, true_and, hxy, ite_mul, zero_mul, and_true, and_false]
  · intro z _ hzx
    rw [rho_projector M hζ hc]
    simp only [Ne.symm hzx, false_and, ↓reduceIte, zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]

end
end OddKaplansky.WreathFourier

end

end OAI
end

section
namespace OAI



section

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {H : Type portUniverse2} [Field K] [sectionInstance13 : Group H] [Fintype H]
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)

include hc in
lemma normal_coordinate (lmb μ : Base (H := H) M) (h g : H) :
    (rho M hζ (normal M hζ μ g) lmb (shift M h⁻¹ lmb)).coeff h =
      if μ = lmb ∧ g = h then 1 else 0 := by
  rw [rho_normal M hζ hc]
  by_cases hgh : g = h
  · subst g
    simp only [shift_shift_inverse, and_true]
    by_cases hml : μ = lmb
    · subst μ; simp only [↓reduceIte, MonoidAlgebra.coeff_single, Finsupp.single_eq_same]
    · simp only [Ne.symm hml, ↓reduceIte, MonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, hml]
  · simp only [hgh, and_false, ite_false]
    split_ifs <;> simp only [MonoidAlgebra.coeff_single, ne_eq, hgh, not_false_eq_true, Finsupp.single_eq_of_ne', MonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]

include hc in
lemma normal_independent : LinearIndependent K (fun a : Base (H := H) M × H => normal M hζ a.1 a.2) := by
  rw [linearIndependent_iff']
  intro s c hs a ha
  have he := congrArg (fun z => (rho M hζ z a.1 (shift M a.2⁻¹ a.1)).coeff a.2) hs
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply,
    MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul, Finset.sum_apply',
    Finsupp.smul_apply, Finsupp.zero_apply, smul_eq_mul, map_zero, Matrix.zero_apply, MonoidAlgebra.coeff_zero] at he
  simp_rw [normal_coordinate M hζ hc] at he
  have hh (b : Base (H := H) M × H) : b.1 = a.1 ∧ b.2 = a.2 ↔ b = a := Prod.ext_iff.symm
  simpa only [hh, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', if_pos ha] using he

instance : Fintype (Wreath (H := H) M) := Fintype.ofFinite _

lemma normal_card
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    [Field.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] : Fintype.card (Base (H := H) M × H) =
    Module.finrank K (MonoidAlgebra K (Wreath (H := H) M)) := by
  rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis _ K)]
  apply Fintype.card_congr
  exact { toFun := fun a => ⟨a.1,a.2⟩
          invFun := fun g => (g.left,g.right)
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }

def normalBasis : Module.Basis (Base (H := H) M × H) K (MonoidAlgebra K (Wreath (H := H) M)) :=
  Module.Basis.mk (normal_independent M hζ hc)
    ((normal_independent M hζ hc).span_eq_top_of_card_eq_finrank' (normal_card (K := K) M)).ge
@[simp] lemma normalBasis_apply (a : Base (H := H) M × H) :
    normalBasis M hζ hc a = normal M hζ a.1 a.2 := Module.Basis.mk_apply _ _ _

end
end OddKaplansky.WreathFourier

end

end OAI
end

section
namespace OAI



section

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {H : Type portUniverse2} [Field K] [Group H] [sectionInstance14 : Fintype H]
variable (M : ℕ) [sectionInstance15 : NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)

@[simp] lemma topElt_mul
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    [Field.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (h g : H) : topElt (K := K) M h * topElt M g = topElt M (h*g) := by
  simp only [topElt, MonoidAlgebra.single_mul_single, ← map_mul, mul_one]
@[simp] lemma topElt_one
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    [Field.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] : topElt (K := K) (H := H) M 1 = 1 := by rw [topElt,map_one]; rfl

lemma topElt_projector (h : H) (lmb : Base (H := H) M) :
    topElt M h * projector M hζ lmb = projector M hζ (shift M h lmb) * topElt M h := by
  calc
    _ = (topElt M h * projector M hζ lmb * topElt M h⁻¹) * topElt M h := by
      rw [mul_assoc _ (topElt M h⁻¹),topElt_mul,inv_mul_cancel,topElt_one,mul_one]
    _ = _ := by rw [translated]

include hc in
lemma normal_mul (lmb μ : Base (H := H) M) (h g : H) :
    normal M hζ lmb h * normal M hζ μ g =
      if lmb = shift M h μ then normal M hζ lmb (h*g) else 0 := by
  unfold normal
  have heq : (projector M hζ lmb * topElt M h) * (projector M hζ μ * topElt M g) =
      (projector M hζ lmb * projector M hζ (shift M h μ)) * (topElt M h * topElt M g) := by
    rw [mul_assoc, ← mul_assoc (topElt M h), topElt_projector]
    simp only [mul_assoc]
  rw [heq,topElt_mul]
  by_cases he : lmb = shift M h μ
  · rw [← he,projector_idempotent M hζ hc,if_pos rfl]
  · rw [projector_orthogonal M hζ _ _ he,zero_mul,if_neg he]

end
end OddKaplansky.WreathFourier

end

end OAI
end

section
namespace OAI



section

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {H : Type portUniverse2} {R : Type portUniverse3} [Field K] [Group H] [Fintype H] [sectionInstance16 : Fintype R]
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
variable (lmb : R → Base (H := H) M)
variable (hinj : Function.Injective (fun a : R × H => shift M a.2 (lmb a.1)))

def freeUnit (a : R × H × H) : MonoidAlgebra K (Wreath (H := H) M) :=
  normal M hζ (shift M a.2.1 (lmb a.1)) (a.2.1*a.2.2⁻¹)

lemma freeUnit_mul
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    {R : Type contextUniverse3}
    [contextInstance3 : Field.{contextUniverse1} K]
    [contextInstance4 : Group.{contextUniverse2} H]
    [contextInstance5 : Fintype.{contextUniverse2} H]
    [Fintype.{contextUniverse3} R]
    (M : Nat)
    [contextInstance8 : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance3)) ζ M)
    (hc : @Ne.{contextUniverse1 + 1} K
  (@Nat.cast.{contextUniverse1} K
    (@AddMonoidWithOne.toNatCast.{contextUniverse1} K
      (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
        (@Ring.toAddGroupWithOne.{contextUniverse1} K
          (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance3)))))
    (@Fintype.card.{contextUniverse2} (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
      (@Pi.instFintype.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M)
        (fun a b => Classical.propDecidable (@Eq.{contextUniverse2 + 1} H a b)) contextInstance5 fun _ =>
        @Multiplicative.fintype.{0} (ZMod M) (@ZMod.fintype M contextInstance8))))
  (@OfNat.ofNat.{contextUniverse1} K (nat_lit 0)
    (@Zero.toOfNat0.{contextUniverse1} K
      (@MulZeroClass.toZero.{contextUniverse1} K
        (@instMulZeroClassOfSemiring.{contextUniverse1} K
          (@CommSemiring.toSemiring.{contextUniverse1} K
            (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3))))))))
    (lmb : R → @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
    (hinj : @Function.Injective.{max (contextUniverse2 + 1) (contextUniverse3 + 1), contextUniverse2 + 1} (Prod.{contextUniverse3, contextUniverse2} R H)
  (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) fun a =>
  @DFunLike.coe.{contextUniverse2 + 1, contextUniverse2 + 1, contextUniverse2 + 1}
    (@MulEquiv.{contextUniverse2, contextUniverse2} (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
      (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
        @Multiplicative.mul.{0} (ZMod M)
          (@Distrib.toAdd.{0} (ZMod M)
            (@instDistribOfSemiring.{0} (ZMod M)
              (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))
      (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
        @Multiplicative.mul.{0} (ZMod M)
          (@Distrib.toAdd.{0} (ZMod M)
            (@instDistribOfSemiring.{0} (ZMod M)
              (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M)))))))
    (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (fun _ => @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
    (@EquivLike.toFunLike.{contextUniverse2 + 1, contextUniverse2 + 1, contextUniverse2 + 1}
      (@MulEquiv.{contextUniverse2, contextUniverse2} (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
        (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
          @Multiplicative.mul.{0} (ZMod M)
            (@Distrib.toAdd.{0} (ZMod M)
              (@instDistribOfSemiring.{0} (ZMod M)
                (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))
        (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
          @Multiplicative.mul.{0} (ZMod M)
            (@Distrib.toAdd.{0} (ZMod M)
              (@instDistribOfSemiring.{0} (ZMod M)
                (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M)))))))
      (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
      (@MulEquiv.instEquivLike.{contextUniverse2, contextUniverse2} (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
        (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
        (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
          @Multiplicative.mul.{0} (ZMod M)
            (@Distrib.toAdd.{0} (ZMod M)
              (@instDistribOfSemiring.{0} (ZMod M)
                (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))
        (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
          @Multiplicative.mul.{0} (ZMod M)
            (@Distrib.toAdd.{0} (ZMod M)
              (@instDistribOfSemiring.{0} (ZMod M)
                (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))))
    (@OddKaplansky.WreathFourier.shift.{contextUniverse2} H contextInstance4 M (@Prod.snd.{contextUniverse3, contextUniverse2} R H a))
    (lmb (@Prod.fst.{contextUniverse3, contextUniverse2} R H a))) (r s : R) (x y z t : H) :
    freeUnit M hζ lmb (r,x,y) * freeUnit M hζ lmb (s,z,t) =
      if r = s ∧ y = z then freeUnit M hζ lmb (r,x,t) else 0 := by
  have he : shift M x (lmb r) = shift M (x*y⁻¹) (shift M z (lmb s)) ↔ r = s ∧ y = z := by
    constructor
    · intro h
      have hh := @hinj (r,x) (s,x*y⁻¹*z) (show shift M x (lmb r) = shift M (x*y⁻¹*z) (lmb s) by simpa only [shift_mul] using h)
      have hr : r = s := congrArg Prod.fst hh
      have hx : x = x*y⁻¹*z := congrArg Prod.snd hh
      refine ⟨hr,?_⟩
      have hy : 1 = y⁻¹*z := mul_left_cancel (by simpa only [mul_assoc,mul_one] using hx)
      exact inv_mul_eq_one.mp hy.symm
    · rintro ⟨rfl,rfl⟩
      rw [← shift_mul]
      simp only [mul_assoc,inv_mul_cancel,mul_one]
  simp only [freeUnit,normal_mul M hζ hc,he]
  split_ifs with h
  · rcases h with ⟨rfl,rfl⟩
    simp only [mul_assoc,inv_mul_cancel_left]
  · rfl

lemma freeUnit_independent
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    {R : Type contextUniverse3}
    [contextInstance3 : Field.{contextUniverse1} K]
    [contextInstance4 : Group.{contextUniverse2} H]
    [contextInstance5 : Fintype.{contextUniverse2} H]
    [Fintype.{contextUniverse3} R]
    (M : Nat)
    [contextInstance8 : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance3)) ζ M)
    (hc : @Ne.{contextUniverse1 + 1} K
  (@Nat.cast.{contextUniverse1} K
    (@AddMonoidWithOne.toNatCast.{contextUniverse1} K
      (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
        (@Ring.toAddGroupWithOne.{contextUniverse1} K
          (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance3)))))
    (@Fintype.card.{contextUniverse2} (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
      (@Pi.instFintype.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M)
        (fun a b => Classical.propDecidable (@Eq.{contextUniverse2 + 1} H a b)) contextInstance5 fun _ =>
        @Multiplicative.fintype.{0} (ZMod M) (@ZMod.fintype M contextInstance8))))
  (@OfNat.ofNat.{contextUniverse1} K (nat_lit 0)
    (@Zero.toOfNat0.{contextUniverse1} K
      (@MulZeroClass.toZero.{contextUniverse1} K
        (@instMulZeroClassOfSemiring.{contextUniverse1} K
          (@CommSemiring.toSemiring.{contextUniverse1} K
            (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3))))))))
    (lmb : R → @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
    (hinj : @Function.Injective.{max (contextUniverse2 + 1) (contextUniverse3 + 1), contextUniverse2 + 1} (Prod.{contextUniverse3, contextUniverse2} R H)
  (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) fun a =>
  @DFunLike.coe.{contextUniverse2 + 1, contextUniverse2 + 1, contextUniverse2 + 1}
    (@MulEquiv.{contextUniverse2, contextUniverse2} (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
      (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
        @Multiplicative.mul.{0} (ZMod M)
          (@Distrib.toAdd.{0} (ZMod M)
            (@instDistribOfSemiring.{0} (ZMod M)
              (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))
      (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
        @Multiplicative.mul.{0} (ZMod M)
          (@Distrib.toAdd.{0} (ZMod M)
            (@instDistribOfSemiring.{0} (ZMod M)
              (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M)))))))
    (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (fun _ => @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
    (@EquivLike.toFunLike.{contextUniverse2 + 1, contextUniverse2 + 1, contextUniverse2 + 1}
      (@MulEquiv.{contextUniverse2, contextUniverse2} (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
        (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
          @Multiplicative.mul.{0} (ZMod M)
            (@Distrib.toAdd.{0} (ZMod M)
              (@instDistribOfSemiring.{0} (ZMod M)
                (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))
        (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
          @Multiplicative.mul.{0} (ZMod M)
            (@Distrib.toAdd.{0} (ZMod M)
              (@instDistribOfSemiring.{0} (ZMod M)
                (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M)))))))
      (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
      (@MulEquiv.instEquivLike.{contextUniverse2, contextUniverse2} (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
        (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
        (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
          @Multiplicative.mul.{0} (ZMod M)
            (@Distrib.toAdd.{0} (ZMod M)
              (@instDistribOfSemiring.{0} (ZMod M)
                (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))
        (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
          @Multiplicative.mul.{0} (ZMod M)
            (@Distrib.toAdd.{0} (ZMod M)
              (@instDistribOfSemiring.{0} (ZMod M)
                (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))))
    (@OddKaplansky.WreathFourier.shift.{contextUniverse2} H contextInstance4 M (@Prod.snd.{contextUniverse3, contextUniverse2} R H a))
    (lmb (@Prod.fst.{contextUniverse3, contextUniverse2} R H a))) : LinearIndependent K (freeUnit M hζ lmb) := by
  let f : R × H × H → Base (H := H) M × H := fun a => (shift M a.2.1 (lmb a.1), a.2.1*a.2.2⁻¹)
  have hf : Function.Injective f := by
    rintro ⟨r,x,y⟩ ⟨s,z,t⟩ he
    have hrs := @hinj (r,x) (s,z) (congrArg Prod.fst he)
    have hr : r = s := congrArg Prod.fst hrs
    have hx : x = z := congrArg Prod.snd hrs
    subst s
    subst z
    have hy : y = t := inv_injective (mul_left_cancel (congrArg Prod.snd he))
    subst t
    rfl
  exact (normal_independent M hζ hc).comp f hf

lemma topElt_normal (h g : H) (μ : Base (H := H) M) :
    topElt M h * normal M hζ μ g = normal M hζ (shift M h μ) (h*g) := by
  unfold normal
  rw [← mul_assoc,topElt_projector,mul_assoc,topElt_mul]

lemma topElt_freeUnit
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    {R : Type contextUniverse3}
    [contextInstance3 : Field.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    [Fintype.{contextUniverse3} R]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance3)) ζ M)
    (lmb : R → @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (h : H) (r : R) (x y : H) :
    topElt M h * freeUnit M hζ lmb (r,x,y) = freeUnit M hζ lmb (r,h*x,y) := by
  simp only [freeUnit,topElt_normal,shift_mul,mul_assoc]

lemma freeUnit_topElt
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    {R : Type contextUniverse3}
    [contextInstance3 : Field.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    [Fintype.{contextUniverse3} R]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance3)) ζ M)
    (lmb : R → @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (h : H) (r : R) (x y : H) :
    freeUnit M hζ lmb (r,x,y) * topElt M h = freeUnit M hζ lmb (r,x,h⁻¹*y) := by
  simp only [freeUnit,normal,mul_assoc,topElt_mul,mul_inv_rev,inv_inv]

def baseElt (a : Base (H := H) M) : MonoidAlgebra K (Wreath (H := H) M) := MonoidAlgebra.single (base M a) 1

lemma projector_baseElt (a μ : Base (H := H) M) :
    projector M hζ μ * baseElt M a = (Fourier.character M hζ μ a : K) • projector M hζ μ :=
  CharacterIdempotents.pushed_mul_single _ _ _

lemma baseElt_projector (a μ : Base (H := H) M) :
    baseElt M a * projector M hζ μ = (Fourier.character M hζ μ a : K) • projector M hζ μ := by
  let f := MonoidAlgebra.mapDomainAlgHom K K (base (H := H) M)
  have hh := congrArg f (mul_comm (MonoidAlgebra.single a (1 : K)) (CharacterIdempotents.projector (Fourier.character M hζ μ)))
  have hf : f (MonoidAlgebra.single a 1) = baseElt M a := by simp only [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single, baseElt, f]
  rw [map_mul,map_mul,hf] at hh
  exact hh.trans (projector_baseElt M hζ a μ)

lemma topElt_baseElt (h : H) (a : Base (H := H) M) :
    topElt (K := K) M h * baseElt M a = baseElt M (shift M h a) * topElt M h := by
  have hg := top_conjugate M h a
  have he := congrArg (fun g : Wreath (H := H) M => g * top M h) hg
  simp only [mul_assoc,inv_mul_cancel,mul_one] at he
  simp only [topElt,baseElt,MonoidAlgebra.single_mul_single,one_mul,he]

lemma baseElt_freeUnit
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    {R : Type contextUniverse3}
    [contextInstance3 : Field.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    [Fintype.{contextUniverse3} R]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance3)) ζ M)
    (lmb : R → @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (a : Base (H := H) M) (r : R) (x y : H) :
    baseElt M a * freeUnit M hζ lmb (r,x,y) =
      (Fourier.character M hζ (shift M x (lmb r)) a : K) • freeUnit M hζ lmb (r,x,y) := by
  simp only [freeUnit,normal,← mul_assoc,baseElt_projector,smul_mul_assoc]

lemma freeUnit_baseElt
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    {R : Type contextUniverse3}
    [contextInstance3 : Field.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    [Fintype.{contextUniverse3} R]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance3)) ζ M)
    (lmb : R → @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (a : Base (H := H) M) (r : R) (x y : H) :
    freeUnit M hζ lmb (r,x,y) * baseElt M a =
      (Fourier.character M hζ (shift M y (lmb r)) a : K) • freeUnit M hζ lmb (r,x,y) := by
  simp only [freeUnit,normal,mul_assoc,topElt_baseElt]
  rw [← mul_assoc,projector_baseElt]
  rw [character_shift_right,← shift_mul]
  simp only [mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one,smul_mul_assoc]
end
end OddKaplansky.WreathFourier

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.MatrixUnits
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {A : Type portUniverse2} {R : Type portUniverse3} {X : Type portUniverse4} {I : Type portUniverse5} [Field K] [Ring A] [Algebra K A]
variable [Fintype R] [Fintype X] [Fintype I]
variable (u : R × X × X → A)

def lift : (R → Matrix X X K) →ₗ[K] A where
  toFun F := ∑ a : R × X × X, F a.1 a.2.1 a.2.2 • u a
  map_add' F G := by simp only [Pi.add_apply, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c F := by simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]
lemma lift_apply (F : R → Matrix X X K) : lift u F = ∑ r, ∑ x, ∑ y, F r x y • u (r,x,y) := by
  simp only [lift,LinearMap.coe_mk,AddHom.coe_mk,Fintype.sum_prod_type]

lemma lift_injective (hu : LinearIndependent K u) : Function.Injective (lift (K := K) u) := by
  intro F G he
  funext r x y
  exact hu.eq_coords_of_eq he (r,x,y)

variable (hprod : ∀ r s x y z t, u (r,x,y) * u (s,z,t) = if r = s ∧ y = z then u (r,x,t) else 0)
include hprod in
lemma lift_mul (F G : R → Matrix X X K) : lift u F * lift u G = lift u (fun r => F r * G r) := by
  have hG (r : R) (x y : X) : u (r,x,y) * lift u G = ∑ t : X, G r y t • u (r,x,t) := by
    simp only [lift_apply, Finset.mul_sum, Algebra.mul_smul_comm, hprod, ite_and, smul_ite, smul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [lift_apply]
  simp only [Finset.sum_mul,smul_mul_assoc,hG]
  rw [lift_apply]
  simp only [Finset.smul_sum,smul_smul,Matrix.mul_apply,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro x _
  exact Finset.sum_comm

include hprod in

lemma regular_rank_bound [FiniteDimensional K A] (hu : LinearIndependent K u)
    (B : Matrix X I K) (C : R → Matrix I X K) (hCB : ∀ r, C r * B = 1) :
    Fintype.card R * Fintype.card I * Fintype.card X ≤
      Module.finrank K (LinearMap.range (Algebra.lmul K A (lift u (fun r => B * C r)))) := by
  let V : (R → Matrix I X K) →ₗ[K] A := {
    toFun F := lift u (fun r => B * F r)
    map_add' F G := by simp only [Pi.add_apply,Matrix.mul_add,← map_add]; rfl
    map_smul' c F := by simp only [Pi.smul_apply,Matrix.mul_smul,← map_smul]; rfl }
  have hV : Function.Injective V := by
    intro F G he
    change lift u (fun r => B*F r) = lift u (fun r => B*G r) at he
    have hh := lift_injective u hu he
    funext r
    have hr := congrArg (fun f : R → Matrix X X K => C r * f r) hh
    simpa only [← Matrix.mul_assoc,hCB,Matrix.one_mul] using hr
  have hsub : LinearMap.range V ≤ LinearMap.range (Algebra.lmul K A (lift u (fun r => B*C r))) := by
    rintro a ⟨F,rfl⟩
    refine ⟨V F,?_⟩
    change lift u (fun r => B*C r) * lift u (fun r => B*F r) = lift u (fun r => B*F r)
    rw [lift_mul u hprod]
    congr 1
    funext r
    calc
      B*C r*(B*F r) = B*(C r*B)*F r := by simp only [Matrix.mul_assoc]
      _ = B*F r := by rw [hCB,Matrix.mul_one]
  have hfin := Submodule.finrank_mono hsub
  rw [LinearMap.finrank_range_of_inj hV] at hfin
  simpa only [Module.finrank_pi_fintype,Module.finrank_matrix,Module.finrank_self,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,mul_one,← mul_assoc] using hfin

include hprod in
lemma lift_idempotent (T : R → Matrix X X K) (hT : ∀ r, T r * T r = T r) :
    lift u T * lift u T = lift u T := by rw [lift_mul u hprod]; congr 1; funext r; exact hT r

end
end OddKaplansky.MatrixUnits

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.MatrixActions
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {A : Type portUniverse2} {S : Type portUniverse3} [CommRing K] [Ring A] [Ring S] [Algebra K A] [Algebra K S]
variable (φ : S →ₗ[K] A)
def Represents (a : A) (s : S) : Prop := ∀ F : S, a * φ F = φ (s*F) ∧ φ F * a = φ (F*s)
lemma represents_one : Represents φ 1 1 := by intro F; simp only [one_mul, mul_one, and_self]
lemma represents_sub {a b : A} {s t : S} (ha : Represents φ a s) (hb : Represents φ b t) :
    Represents φ (a-b) (s-t) := by
  intro F
  constructor
  · rw [sub_mul,(ha F).1,(hb F).1,sub_mul,map_sub]
  · rw [mul_sub,(ha F).2,(hb F).2,mul_sub,map_sub]
lemma represents_mul {a b : A} {s t : S} (ha : Represents φ a s) (hb : Represents φ b t) :
    Represents φ (a*b) (s*t) := by
  intro F
  constructor
  · rw [mul_assoc,(hb F).1,(ha (t*F)).1,mul_assoc]
  · rw [← mul_assoc,(ha F).2,(hb (F*s)).2,mul_assoc]
lemma represents_pow {a : A} {s : S} (ha : Represents φ a s) (n : ℕ) : Represents φ (a^n) (s^n) := by
  induction n with
  | zero => simpa only [pow_zero] using represents_one φ
  | succ n ih => simpa only [pow_succ] using represents_mul φ ih ha
lemma annihilates_left {a : A} {s F : S} (ha : Represents φ a s) (hs : s*F=0) : a*φ F=0 := by rw [(ha F).1,hs,map_zero]
lemma annihilates_right {a : A} {s F : S} (ha : Represents φ a s) (hs : F*s=0) : φ F*a=0 := by rw [(ha F).2,hs,map_zero]
end
end OddKaplansky.MatrixActions

namespace OddKaplansky.TranslationMatrix
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse4} {H : Type portUniverse5} [CommRing K] [Group H] [sectionInstance17 : Fintype H]
def matrix (h : H) : Matrix H H K := fun x y => if x=h*y then 1 else 0
lemma mul_apply (h : H) {J : Type portUniverse6} (A : Matrix H J K) (x : H) (y : J) : (matrix (K := K) h * A) x y = A (h⁻¹*x) y := by
  rw [Matrix.mul_apply,Finset.sum_eq_single (h⁻¹*x)]
  · simp only [matrix, mul_inv_cancel_left, ↓reduceIte, one_mul]
  · intro b _ hb
    have he : x ≠ h*b := by intro he; apply hb; rw [he,inv_mul_cancel_left]
    simp only [matrix, he, ↓reduceIte, zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]
lemma right_mul_apply (h : H) {J : Type portUniverse7} [Fintype J] (A : Matrix J H K) (x : J) (y : H) :
    (A * matrix (K := K) h) x y = A x (h*y) := by simp only [Matrix.mul_apply, matrix, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
end
end OddKaplansky.TranslationMatrix

end

end OAI
end

section
namespace OAI



section

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {H : Type portUniverse2} {R : Type portUniverse3} [Field K] [Group H] [Fintype H] [sectionInstance18 : Fintype R]
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (lmb : R → Base (H := H) M)
local notation "φ" => MatrixUnits.lift (K := K) (freeUnit M hζ lmb)

def diagonal (a : Base (H := H) M) (r : R) : Matrix H H K :=
  Matrix.diagonal (fun x => (Fourier.character M hζ (shift M x (lmb r)) a : K))

lemma top_represents (h : H) : MatrixActions.Represents φ (topElt M h) (fun _ : R => TranslationMatrix.matrix (K := K) h) := by
  intro F
  constructor
  · rw [MatrixUnits.lift_apply,MatrixUnits.lift_apply]
    simp only [Finset.mul_sum,mul_smul_comm,topElt_freeUnit]
    apply Finset.sum_congr rfl
    intro r _
    simp only [Pi.mul_apply,TranslationMatrix.mul_apply]
    have he := Equiv.sum_comp (Equiv.mulLeft h) (fun x : H => ∑ y : H, F r (h⁻¹*x) y • freeUnit M hζ lmb (r,x,y))
    simpa only [Equiv.coe_mulLeft,inv_mul_cancel_left] using he
  · rw [MatrixUnits.lift_apply,MatrixUnits.lift_apply]
    simp only [Finset.sum_mul,smul_mul_assoc,freeUnit_topElt]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro x _
    simp only [Pi.mul_apply,TranslationMatrix.right_mul_apply]
    have he := Equiv.sum_comp (Equiv.mulLeft h⁻¹) (fun y : H => F r x (h*y) • freeUnit M hζ lmb (r,x,y))
    simpa only [Equiv.coe_mulLeft,mul_inv_cancel_left] using he

lemma base_represents (a : Base (H := H) M) : MatrixActions.Represents φ (baseElt M a) (diagonal M hζ lmb a) := by
  intro F
  constructor
  · simp only [MatrixUnits.lift_apply,Finset.mul_sum,mul_smul_comm,baseElt_freeUnit,smul_smul,Pi.mul_apply,diagonal,Matrix.diagonal_mul,mul_comm]
  · simp only [MatrixUnits.lift_apply,Finset.sum_mul,smul_mul_assoc,freeUnit_baseElt,smul_smul,Pi.mul_apply,diagonal,Matrix.mul_diagonal]

lemma diagonal_inv
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    {R : Type contextUniverse3}
    [contextInstance3 : Field.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    [Fintype.{contextUniverse3} R]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance3)) ζ M)
    (lmb : R → @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (a : Base (H := H) M) (r : R) :
    diagonal M hζ lmb a r * diagonal M hζ lmb a⁻¹ r = 1 := by
  rw [diagonal,diagonal,Matrix.diagonal_mul_diagonal]
  simp only [map_inv,Units.val_inv_eq_inv_val,mul_inv_cancel₀ (Units.ne_zero _),Matrix.diagonal_one]

lemma diagonal_inv' (a : Base (H := H) M) (r : R) :
    diagonal M hζ lmb a⁻¹ r * diagonal M hζ lmb a r = 1 := by simpa only [inv_inv] using diagonal_inv M hζ lmb a⁻¹ r

lemma conjugate_represents (a : Base (H := H) M) (h : H) :
    MatrixActions.Represents φ (baseElt M a * topElt M h * baseElt M a⁻¹)
      (fun r => diagonal M hζ lmb a r * TranslationMatrix.matrix h * diagonal M hζ lmb a⁻¹ r) :=
  MatrixActions.represents_mul φ (MatrixActions.represents_mul φ (base_represents M hζ lmb a) (top_represents M hζ lmb h)) (base_represents M hζ lmb a⁻¹)
end
end OddKaplansky.WreathFourier

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.FreeShiftCount
noncomputable section
open scoped Classical BigOperators
variable {X : Type portUniverse1} {C : Type portUniverse2} [Fintype X] [Fintype C]

lemma card_equal_coordinate (a b : X) (hab : a ≠ b) :
    Fintype.card {f : X → C // f a = f b} * Fintype.card C ≤ Fintype.card C ^ Fintype.card X := by
  let r : {f : X → C // f a = f b} → ({x : X // x ≠ a} → C) := fun f x => f.val x.val
  have hr : Function.Injective r := by
    intro f g he
    apply Subtype.ext
    funext x
    by_cases hx : x = a
    · subst x
      have he' : f.val b = g.val b := congrFun he ⟨b,Ne.symm hab⟩
      exact f.property.trans (he'.trans g.property.symm)
    · exact congrFun he ⟨x,hx⟩
  have hh := Fintype.card_le_of_injective r hr
  rw [Fintype.card_fun] at hh
  have hc := Fintype.card_congr (Equiv.optionSubtypeNe a)
  rw [Fintype.card_option] at hc
  calc
    _ ≤ Fintype.card C ^ Fintype.card {x : X // x ≠ a} * Fintype.card C := Nat.mul_le_mul_right _ hh
    _ = _ := by rw [← pow_succ,hc]

variable {H : Type portUniverse3} [Group H] [Fintype H]
def Free (f : H → C) : Prop := ∀ g : H, (∀ x, f (g⁻¹*x) = f x) → g = 1

lemma card_not_free :
    Fintype.card {f : H → C // ¬ Free f} * Fintype.card C ≤
      (Fintype.card H - 1) * Fintype.card C ^ Fintype.card H := by
  let F (g : H) := {f : H → C | ∀ x, f (g⁻¹*x) = f x}
  have hFg (g : H) (hg : g ≠ 1) : Fintype.card (F g) * Fintype.card C ≤ Fintype.card C ^ Fintype.card H := by
    have hi : Fintype.card (F g) ≤ Fintype.card {f : H → C // f 1 = f g⁻¹} := by
      apply Fintype.card_le_of_injective (fun f => ⟨f.val,by simpa only [mul_one] using (f.property 1).symm⟩)
      intro f t he
      exact Subtype.ext (congrArg (fun q : {f : H → C // f 1 = f g⁻¹} => q.val) he)
    apply (Nat.mul_le_mul_right _ hi).trans
    exact card_equal_coordinate 1 g⁻¹ (by simpa only [ne_eq, one_eq_inv] using hg)
  let U := (Finset.univ.erase (1 : H)).biUnion (fun g => Finset.univ.filter (fun f : H → C => f ∈ F g))
  have hU : U = Finset.univ.filter (fun f : H → C => ¬ Free f) := by
    ext f
    simp only [U, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_filter,true_and,F,Set.mem_ofPred_eq,Free]
    simp only [not_forall]
    first | (simp only [Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]; exact ⟨fun ⟨g, hg, hf⟩ => ⟨g, hf, hg⟩, fun ⟨g, hf, hg⟩ => ⟨g, hg, hf⟩⟩) | aesop
  have hcard : Fintype.card {f : H → C // ¬ Free f} = U.card := by
    rw [hU]
    exact Fintype.card_subtype _
  rw [hcard]
  calc
    U.card * Fintype.card C ≤ (∑ g ∈ Finset.univ.erase (1 : H), (Finset.univ.filter (fun f : H → C => f ∈ F g)).card) * Fintype.card C :=
      Nat.mul_le_mul_right _ (Finset.card_biUnion_le)
    _ = ∑ g ∈ Finset.univ.erase (1 : H), (Finset.univ.filter (fun f : H → C => f ∈ F g)).card * Fintype.card C := by rw [Finset.sum_mul]
    _ ≤ ∑ _g ∈ Finset.univ.erase (1 : H), Fintype.card C ^ Fintype.card H := by
      apply Finset.sum_le_sum
      intro g hg
      rw [← Fintype.card_subtype]
      exact hFg g (Finset.mem_erase.mp hg).1
    _ = _ := by simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ (1 : H)), Finset.card_univ, smul_eq_mul]
end
end OddKaplansky.FreeShiftCount

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.WeightedGram
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {X : Type portUniverse2} {I : Type portUniverse3} [Field K] [Fintype X] [sectionInstance20 : Fintype I] [sectionInstance19 : DecidableEq X] [sectionInstance21 : DecidableEq I]

lemma exists_minor
    {K : Type contextUniverse1}
    {X : Type contextUniverse2}
    {I : Type contextUniverse3}
    [Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} X]
    [Fintype.{contextUniverse3} I]
    [DecidableEq.{contextUniverse2 + 1} X]
    [DecidableEq.{contextUniverse3 + 1} I] (B : Matrix X I K) (hB : LinearIndependent K B.col) :
    ∃ f : I ↪ X, (B.submatrix f id).det ≠ 0 := by
  have hr : B.rank = Fintype.card I := by
    rw [← B.rank_transpose]
    exact hB.rank_matrix
  have ht : Submodule.span K (Set.range B.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← B.rank_eq_finrank_span_row, hr, Module.finrank_pi]
  let b := Module.Basis.ofSpan ht.ge
  let e := b.indexEquiv (Pi.basisFun K I)
  let b' := b.reindex e
  have hb (i : I) : ∃ x, B.row x = b' i := by
    exact Module.Basis.ofSpan_subset ht.ge ⟨e.symm i, (Module.Basis.reindex_apply b e i).symm⟩
  choose f hf using hb
  have hfi : Function.Injective f := by
    intro i j hij
    apply b'.injective
    rw [← hf, ← hf, hij]
  refine ⟨⟨f,hfi⟩, Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.linearIndependent_row_iff.mp ?_)⟩
  change LinearIndependent K (fun i => B.row (f i))
  have he : (fun i => B.row (f i)) = b' := funext hf
  rw [he]
  exact b'.linearIndependent

lemma gram_entry
    {X : Type contextUniverse1}
    {I : Type contextUniverse2}
    [Fintype.{contextUniverse1} X]
    [Fintype.{contextUniverse2} I]
    [DecidableEq.{contextUniverse1 + 1} X]
    [DecidableEq.{contextUniverse2 + 1} I] {A : Type portUniverse4} [CommRing A] (B : Matrix X I A) (τ : X → A) (i j : I) :
    (B.transpose * Matrix.diagonal τ * B) i j = ∑ x : X, B x i * τ x * B x j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

def polynomial (B : Matrix X I K) : MvPolynomial X K :=
  ((B.transpose.map (MvPolynomial.C : K →+* MvPolynomial X K)) * Matrix.diagonal (fun x => (MvPolynomial.X x : MvPolynomial X K)) *
    B.map (MvPolynomial.C : K →+* MvPolynomial X K)).det

lemma eval_polynomial (B : Matrix X I K) (τ : X → K) :
    MvPolynomial.eval τ (polynomial B) = (B.transpose * Matrix.diagonal τ * B).det := by
  rw [polynomial, (MvPolynomial.eval τ).map_det]
  congr 1
  apply Matrix.ext
  intro i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

lemma nonzero (B : Matrix X I K) (hB : LinearIndependent K B.col) : polynomial B ≠ 0 := by
  obtain ⟨f,hf⟩ := exists_minor B hB
  let τ : X → K := fun x => if x ∈ Set.range f then 1 else 0
  have he : B.transpose * Matrix.diagonal τ * B = (B.submatrix f id).transpose * (B.submatrix f id) := by
    apply Matrix.ext
    intro i j
    rw [gram_entry]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
    calc
      _ = ∑ x ∈ Finset.univ.image f, B x i * τ x * B x j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro x _ hx
        have hx' : x ∉ Set.range f := by simpa only [Set.mem_range, not_exists, Finset.mem_image, Finset.mem_univ, true_and] using hx
        simp only [τ, if_neg hx', mul_zero, zero_mul]
      _ = ∑ k : I, B (f k) i * B (f k) j := by
        rw [Finset.sum_image f.injective.injOn]
        simp only [Set.mem_range, EmbeddingLike.apply_eq_iff_eq, exists_eq, ↓reduceIte, mul_one, τ]
  intro hz
  have hh := eval_polynomial B τ
  rw [hz,map_zero,he,Matrix.det_mul,Matrix.det_transpose] at hh
  exact (mul_ne_zero hf hf) hh.symm

lemma totalDegree (B : Matrix X I K) : (polynomial B).totalDegree ≤ Fintype.card I := by
  unfold polynomial
  rw [Matrix.det_apply']
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  have hc : (↑(Equiv.Perm.sign σ) : MvPolynomial X K).totalDegree = 0 := by
    simpa only [map_intCast] using (MvPolynomial.totalDegree_C (Equiv.Perm.sign σ : K))
  rw [hc,zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _i : I, 1 := by
      apply Finset.sum_le_sum
      intro i _
      change (( (B.map (MvPolynomial.C : K →+* MvPolynomial X K)).transpose *
        Matrix.diagonal (fun x => (MvPolynomial.X x : MvPolynomial X K)) * B.map (MvPolynomial.C : K →+* MvPolynomial X K)) (σ i) i).totalDegree ≤ 1
      rw [gram_entry]
      simp only [Matrix.map_apply]
      apply MvPolynomial.totalDegree_finsetSum_le
      intro x _
      exact (MvPolynomial.totalDegree_mul _ _).trans (by
        have h := MvPolynomial.totalDegree_mul (MvPolynomial.C (B x (σ i))) (MvPolynomial.X x : MvPolynomial X K)
        simpa only [MvPolynomial.totalDegree_C, add_zero, ge_iff_le, MvPolynomial.totalDegree_X, zero_add] using h)
    _ = Fintype.card I := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

end
end OddKaplansky.WeightedGram

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.PolynomialGrid
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} [Field K] [Fintype K] [DecidableEq K]

lemma card_units_zero_le (n : ℕ) (P : MvPolynomial (Fin n) K) (hP : P ≠ 0) :
    Fintype.card {f : Fin n → Kˣ // MvPolynomial.eval (fun i => (f i : K)) P = 0} * Fintype.card Kˣ ≤
      P.totalDegree * Fintype.card Kˣ ^ n := by
  let S : Finset K := Finset.univ.erase 0
  let Z := {f ∈ Fintype.piFinset (fun _ : Fin n => S) | MvPolynomial.eval f P = 0}
  have hS : S.card = Fintype.card Kˣ := by
    simp only [S,Finset.card_erase_of_mem (Finset.mem_univ (0 : K)),Finset.card_univ]
    exact (Fintype.card_units (α := K)).symm
  let e : {f : Fin n → Kˣ // MvPolynomial.eval (fun i => (f i : K)) P = 0} ≃ Z := {
    toFun := fun f => ⟨fun i => (f.val i : K), by
      apply Finset.mem_filter.mpr
      constructor
      · apply Fintype.mem_piFinset.mpr
        intro i
        simp only [S, Finset.mem_erase,Finset.mem_univ,and_true]
        exact Units.ne_zero _
      · exact f.property⟩
    invFun := fun f => ⟨fun i => Units.mk0 (f.val i) (by
      have h := (Fintype.mem_piFinset.mp (Finset.mem_filter.mp f.property).1) i
      exact (Finset.mem_erase.mp h).1), (Finset.mem_filter.mp f.property).2⟩
    left_inv := fun f => by ext i; rfl
    right_inv := fun f => rfl }
  have hz : Fintype.card {f : Fin n → Kˣ // MvPolynomial.eval (fun i => (f i : K)) P = 0} = Z.card :=
    (Fintype.card_congr e).trans (Fintype.card_coe Z)
  have hs := MvPolynomial.schwartz_zippel_totalDegree hP S
  change (Z.card : ℚ≥0)/(S.card : ℚ≥0)^n ≤ (P.totalDegree : ℚ≥0)/S.card at hs
  have hp : (0 : ℚ≥0) < S.card := by rw [hS]; exact_mod_cast Fintype.card_pos (α := Kˣ)
  have hm := (div_le_div_iff₀ (pow_pos hp n) hp).mp hs
  rw [hz,← hS]
  exact_mod_cast hm

lemma card_units_zero_le_general {X : Type portUniverse2} [Fintype X] (P : MvPolynomial X K) (hP : P ≠ 0) :
    Fintype.card {f : X → Kˣ // MvPolynomial.eval (fun i => (f i : K)) P = 0} * Fintype.card Kˣ ≤
      P.totalDegree * Fintype.card Kˣ ^ Fintype.card X := by
  let e := Fintype.equivFin X
  let Q := MvPolynomial.rename e P
  have hQ : Q ≠ 0 := by
    intro h
    apply hP
    apply MvPolynomial.rename_injective e e.injective
    simpa only [map_zero] using h
  let E : {f : X → Kˣ // MvPolynomial.eval (fun i => (f i : K)) P = 0} ≃
      {f : Fin (Fintype.card X) → Kˣ // MvPolynomial.eval (fun i => (f i : K)) Q = 0} := {
    toFun := fun f => ⟨fun i => f.val (e.symm i),by
      simpa only [Q,MvPolynomial.eval_rename,Function.comp_def,Equiv.symm_apply_apply] using f.property⟩
    invFun := fun f => ⟨fun i => f.val (e i),by
      simpa only [Q,MvPolynomial.eval_rename,Function.comp_def] using f.property⟩
    left_inv := fun f => by ext i; simp only [Equiv.symm_apply_apply]
    right_inv := fun f => by ext i; simp only [Equiv.apply_symm_apply] }
  have h := card_units_zero_le (Fintype.card X) Q hQ
  rw [← Fintype.card_congr E] at h
  exact h.trans (Nat.mul_le_mul_right _ (MvPolynomial.totalDegree_rename_le e P))

end
end OddKaplansky.PolynomialGrid

end

end OAI
end

section
namespace OAI



section

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {H : Type portUniverse2} {I : Type portUniverse3} [Field K] [Fintype K] [Group H] [sectionInstance22 : Fintype H] [Fintype I]
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hM : Fintype.card Kˣ = M)

def weight (lmb : Base (H := H) M) (x : H) : Kˣ :=
  (Fourier.cyclicCharacter M hζ (lmb x⁻¹))⁻¹

lemma weight_bijective
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [contextInstance3 : Fintype.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance2)) ζ M)
    (hM : @Eq.{1} Nat
  (@Fintype.card.{contextUniverse1}
    (@Units.{contextUniverse1} K
      (@Semiring.toMonoid.{contextUniverse1} K
        (@CommSemiring.toSemiring.{contextUniverse1} K
          (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance2)))))
    (@instFintypeUnitsOfDecidableEq.{contextUniverse1} K
      (@Semiring.toMonoid.{contextUniverse1} K
        (@CommSemiring.toSemiring.{contextUniverse1} K
          (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance2))))
      contextInstance3 fun a b => Classical.propDecidable (@Eq.{contextUniverse1 + 1} K a b)))
  M) : Function.Bijective (weight (H := H) M hζ) := by
  have hχ : Function.Bijective (Fourier.cyclicCharacter M hζ) := by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    constructor
    · exact Fourier.cyclicCharacter_injective M hζ
    · simpa only [Fourier.C,Fintype.card_multiplicative,ZMod.card] using hM.symm
  constructor
  · intro lmb μ he
    funext x
    apply hχ.injective
    have hh := congrFun he x⁻¹
    simpa only [weight,inv_inv] using congrArg Inv.inv hh
  · intro f
    choose a ha using fun x => hχ.surjective ((f x⁻¹)⁻¹)
    refine ⟨a,?_⟩
    funext x
    simp only [weight,ha,inv_inv]

variable [DecidableEq H] [DecidableEq I]
def Admissible (B : Matrix H I K) (lmb : Base (H := H) M) : Prop :=
  FreeShiftCount.Free lmb ∧ (B.transpose * Matrix.diagonal (fun x => (weight M hζ lmb x : K)) * B).det ≠ 0

include hM in
lemma card_singular (B : Matrix H I K) (hB : LinearIndependent K B.col) :
    Fintype.card {lmb : Base (H := H) M // (B.transpose * Matrix.diagonal (fun x => (weight M hζ lmb x : K)) * B).det = 0} * M ≤
      Fintype.card I * M ^ Fintype.card H := by
  let E := Equiv.ofBijective (weight (H := H) M hζ) (weight_bijective M hζ hM)
  let E' : {lmb : Base (H := H) M // (B.transpose * Matrix.diagonal (fun x => (weight M hζ lmb x : K)) * B).det = 0} ≃
      {f : H → Kˣ // MvPolynomial.eval (fun x => (f x : K)) (WeightedGram.polynomial B) = 0} :=
    E.subtypeEquiv (fun lmb => by rw [WeightedGram.eval_polynomial]; rfl)
  have hz := PolynomialGrid.card_units_zero_le_general (WeightedGram.polynomial B) (WeightedGram.nonzero B hB)
  have he := Fintype.card_congr E'
  simp only [Fintype.card_eq_nat_card] at he hz ⊢
  have hM' := hM
  simp only [Fintype.card_eq_nat_card] at hM'
  rw [← he,hM'] at hz
  have hd := WeightedGram.totalDegree B
  simp only [Fintype.card_eq_nat_card] at hd
  exact hz.trans (Nat.mul_le_mul_right _ hd)

include hM in
lemma cardinality (B : Matrix H I K) (hB : LinearIndependent K B.col)
    (hI : 4*Fintype.card I < M) (hH : 4*(Fintype.card H-1) < M) :
    Fintype.card (Base (H := H) M) < 2 * Fintype.card {lmb : Base (H := H) M // Admissible M hζ B lmb} := by
  let A := Base (H := H) M
  have hc : Fintype.card (Fourier.C M) = M := by simp only [Fourier.C, Fintype.card_multiplicative, ZMod.card]
  have h0 : 0 < M ^ Fintype.card H := pow_pos (Nat.pos_of_ne_zero (NeZero.ne M)) _
  have hn := FreeShiftCount.card_not_free (H := H) (C := Fourier.C M)
  rw [hc] at hn
  have hs := card_singular M hζ hM B hB
  have hu : Fintype.card {lmb : A // ¬ Admissible M hζ B lmb} ≤
      Fintype.card {lmb : A // ¬ FreeShiftCount.Free lmb} +
      Fintype.card {lmb : A // (B.transpose * Matrix.diagonal (fun x => (weight M hζ lmb x : K)) * B).det = 0} := by
    let f : {lmb : A // ¬ Admissible M hζ B lmb} →
        {lmb : A // ¬ FreeShiftCount.Free lmb} ⊕
        {lmb : A // (B.transpose * Matrix.diagonal (fun x => (weight M hζ lmb x : K)) * B).det = 0} :=
      fun lmb => if h : FreeShiftCount.Free lmb.val then Sum.inr ⟨lmb.val,by simpa only [Admissible,h,true_and,not_not] using lmb.property⟩
      else Sum.inl ⟨lmb.val,h⟩
    have hf : Function.Injective f := by
      intro a b he
      apply Subtype.ext
      have h := congrArg (Sum.elim Subtype.val Subtype.val) he
      simpa only [f,apply_dite,Sum.elim_inl,Sum.elim_inr,dite_eq_ite,ite_self] using h
    simpa only [Fintype.card_sum] using Fintype.card_le_of_injective f hf
  have hc' : Fintype.card {lmb : A // Admissible M hζ B lmb} +
      Fintype.card {lmb : A // ¬ Admissible M hζ B lmb} = M ^ Fintype.card H := by
    rw [Fintype.card_subtype_compl, Nat.add_sub_of_le (Fintype.card_subtype_le _)]
    simp only [A,Base,Fintype.card_fun,hc]
  have hsum : 2*(Fintype.card I+(Fintype.card H-1)) < M := by omega
  have hmul := Nat.mul_lt_mul_of_pos_right hsum h0
  have hub := Nat.mul_le_mul_right M hu
  have hh : 2*Fintype.card {lmb : A // ¬ Admissible M hζ B lmb} < M ^ Fintype.card H := by
    have hp : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    simp only [A, Fintype.card_eq_nat_card] at hn hs hub hmul ⊢
    apply Nat.lt_of_mul_lt_mul_right (a := M)
    first | linarith only [hub, hn, hs, hmul] | nlinarith
  change Fintype.card A < _
  have hca : Fintype.card A = M ^ Fintype.card H := by simp only [A,Base,Fintype.card_fun,hc]
  rw [hca]
  simp only [A, Fintype.card_eq_nat_card] at hc' hh ⊢
  omega
end
end OddKaplansky.WreathFourier

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.WeightedProjection
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {X : Type portUniverse2} {I : Type portUniverse3} [Field K] [Fintype X] [sectionInstance23 : Fintype I] [DecidableEq X] [sectionInstance24 : DecidableEq I]
def gram (B : Matrix X I K) (τ : X → K) := B.transpose * Matrix.diagonal τ * B
def projection (B : Matrix X I K) (τ : X → K) := B * (gram B τ)⁻¹ * B.transpose * Matrix.diagonal τ

lemma fixes (B : Matrix X I K) (τ : X → K) (h : (gram B τ).det ≠ 0) : projection B τ * B = B := by
  have hi := Matrix.nonsing_inv_mul (gram B τ) (isUnit_iff_ne_zero.mpr h)
  simpa only [projection,gram,Matrix.mul_assoc,Matrix.mul_one] using congrArg (fun A => B * A) hi

lemma idempotent (B : Matrix X I K) (τ : X → K) (h : (gram B τ).det ≠ 0) :
    projection B τ * projection B τ = projection B τ := by
  calc
    _ = (projection B τ * B) * (gram B τ)⁻¹ * B.transpose * Matrix.diagonal τ := by simp only [projection, Matrix.mul_assoc]
    _ = _ := by rw [fixes B τ h]; rfl

lemma annihilate_left (B : Matrix X I K) (τ : X → K) (A : Matrix X X K) (h : A * B = 0) :
    A * projection B τ = 0 := by
  simp only [projection,← Matrix.mul_assoc,h,Matrix.zero_mul]

lemma annihilate_right (B : Matrix X I K) (τ : X → K) (A : Matrix X X K)
    (h : B.transpose * Matrix.diagonal τ * A = 0) : projection B τ * A = 0 := by
  calc
    _ = (B * (gram B τ)⁻¹) * (B.transpose * Matrix.diagonal τ * A) := by simp only [Matrix.mul_assoc,projection]
    _ = 0 := by rw [h,Matrix.mul_zero]

lemma conjugate_sub_pow (D D' A : Matrix X X K) (hD : D * D' = 1) (hD' : D' * D = 1) (ell : ℕ) :
    (D*A*D' - 1)^ell = D*(A-1)^ell*D' := by
  induction ell with
  | zero => simpa only [pow_zero, mul_one] using hD.symm
  | succ n ih =>
    rw [pow_succ,ih,pow_succ]
    have hs : D*A*D'-1 = D*(A-1)*D' := by simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_one,hD]
    rw [hs]
    calc
      _ = D * (A-1)^n * (D'*D) * (A-1) * D' := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hD',Matrix.mul_one]; simp only [Matrix.mul_assoc]

lemma conjugate_annihilate
    {K : Type contextUniverse1}
    {X : Type contextUniverse2}
    {I : Type contextUniverse3}
    [Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} X]
    [Fintype.{contextUniverse3} I]
    [DecidableEq.{contextUniverse2 + 1} X]
    [DecidableEq.{contextUniverse3 + 1} I] (B : Matrix X I K) (D D' A : Matrix X X K)
    (hD : D * D' = 1) (hD' : D' * D = 1) (ell : ℕ) (hB : B.transpose * (A-1)^ell = 0) :
    B.transpose * D' * (D*A*D'-1)^ell = 0 := by
  rw [conjugate_sub_pow D D' A hD hD']
  calc
    _ = B.transpose * (D'*D) * (A-1)^ell * D' := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hD',Matrix.mul_one,hB,Matrix.zero_mul]
end
end OddKaplansky.WeightedProjection

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.OrbitSelection
noncomputable section
open scoped Classical BigOperators
variable {H : Type portUniverse1} {A : Type portUniverse2} [Group H] [sectionInstance25 : Fintype H] [sectionInstance26 : Fintype A] [MulAction H A]
variable (good : A → Prop)
abbrev Rep := {q : MulAction.orbitRel.Quotient H A // ∃ a : A, (Quotient.mk'' a : MulAction.orbitRel.Quotient H A) = q ∧ good a}
instance : Fintype (Rep (H := H) good) := Fintype.ofFinite _

def representative (r : Rep (H := H) good) : A := r.property.choose
lemma representative_spec
    {H : Type contextUniverse1}
    {A : Type contextUniverse2}
    [contextInstance2 : Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    [Fintype.{contextUniverse2} A]
    [@MulAction.{contextUniverse1, contextUniverse2} H A (@DivInvMonoid.toMonoid.{contextUniverse1} H (@Group.toDivInvMonoid.{contextUniverse1} H contextInstance2))]
    (good : A → Prop) (r : Rep (H := H) good) :
    (Quotient.mk'' (representative good r) : MulAction.orbitRel.Quotient H A) = r.val ∧ good (representative good r) := r.property.choose_spec

lemma cover (a : A) (ha : good a) : ∃ r : Rep (H := H) good, ∃ h : H, h • representative good r = a := by
  let r : Rep (H := H) good := ⟨Quotient.mk'' a,⟨a,rfl,ha⟩⟩
  refine ⟨r,?_⟩
  have hh : (Quotient.mk'' a : MulAction.orbitRel.Quotient H A) = Quotient.mk'' (representative good r) :=
    (representative_spec good r).1.symm
  exact Quotient.exact hh

lemma card_good : Fintype.card {a : A // good a} ≤ Fintype.card (Rep (H := H) good) * Fintype.card H := by
  choose r h he using fun a : {a : A // good a} => cover (H := H) good a.val a.property
  have hi : Function.Injective (fun a => (r a,h a)) := by
    intro a b hab
    apply Subtype.ext
    rw [← he a,← he b]
    exact congrArg (fun z : Rep (H := H) good × H => z.2 • representative good z.1) hab
  simpa only [Fintype.card_prod] using Fintype.card_le_of_injective _ hi

end
end OddKaplansky.OrbitSelection

end

end OAI
end

section
namespace OAI



section

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {H : Type portUniverse2} {I : Type portUniverse3} [Field K] [sectionInstance27 : Fintype K] [Group H] [Fintype H] [Fintype I]
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)

@[instance_reducible]
def shiftAction : MulAction H (Base (H := H) M) where
  smul h a := shift M h a
  one_smul a := by change shift M 1 a = a; rw [shift_one]; rfl
  mul_smul h g a := shift_mul M h g a

def lamp : Base (H := H) M := Pi.mulSingle 1 (Multiplicative.ofAdd (1 : ZMod M))
lemma weight_diagonal
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance2)) ζ M) {J : Type portUniverse4} [Fintype J] (lmb : J → Base (H := H) M) (r : J) :
    diagonal M hζ lmb (lamp (H := H) M)⁻¹ r = Matrix.diagonal (fun x => (weight M hζ (lmb r) x : K)) := by
  unfold diagonal
  congr 1
  funext x
  simp only [map_inv,Units.val_inv_eq_inv_val,lamp,Fourier.character_mulSingle,shift_apply,mul_one,weight,Units.val_inv_eq_inv_val]

namespace Blocks
variable {R : Type portUniverse5} [Fintype R] (B : Matrix H I K) (lmb : R → Base (H := H) M)
def weights (r : R) (x : H) : K := weight M hζ (lmb r) x
def projection (r : R) := WeightedProjection.projection B (weights M hζ lmb r)
def element := MatrixUnits.lift (K := K) (freeUnit M hζ lmb) (projection M hζ B lmb)
lemma idempotent
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    {I : Type contextUniverse3}
    [contextInstance3 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    [Fintype.{contextUniverse3} I]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance3)) ζ M)
    {R : Type contextUniverse4}
    [Fintype.{contextUniverse4} R]
    (B : Matrix.{contextUniverse2, contextUniverse3, contextUniverse1} H I K)
    (lmb : R → @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
    (hinj : Function.Injective (fun a : R × H => shift M a.2 (lmb a.1)))
    (hN : ∀ r, (WeightedProjection.gram B (weights M hζ lmb r)).det ≠ 0) :
    element M hζ B lmb * element M hζ B lmb = element M hζ B lmb := by
  unfold element
  apply MatrixUnits.lift_idempotent (freeUnit M hζ lmb) (freeUnit_mul M hζ hc lmb hinj) (projection M hζ B lmb)
  intro r
  exact WeightedProjection.idempotent B (weights M hζ lmb r) (hN r)
lemma annihilate (ell : ℕ) (hleft : ∀ s : H, (TranslationMatrix.matrix (K := K) s - 1)^ell * B = 0)
    (hright : ∀ s : H, B.transpose * (TranslationMatrix.matrix (K := K) s - 1)^ell = 0) (s : H) :
    (topElt M s-1)^ell*element M hζ B lmb=0 ∧
    element M hζ B lmb*(baseElt M (lamp (H := H) M)*topElt M s*baseElt M (lamp (H := H) M)⁻¹-1)^ell=0 := by
  let φ := MatrixUnits.lift (K := K) (freeUnit M hζ lmb)
  have hu := MatrixActions.represents_pow φ (MatrixActions.represents_sub φ (top_represents M hζ lmb s) (MatrixActions.represents_one φ)) ell
  have hv := MatrixActions.represents_pow φ (MatrixActions.represents_sub φ (conjugate_represents M hζ lmb (lamp (H := H) M) s) (MatrixActions.represents_one φ)) ell
  constructor
  · apply MatrixActions.annihilates_left φ hu
    funext r
    exact WeightedProjection.annihilate_left B (weights M hζ lmb r) _ (hleft s)
  · apply MatrixActions.annihilates_right φ hv
    funext r
    apply WeightedProjection.annihilate_right B (weights M hζ lmb r)
    change B.transpose * Matrix.diagonal (fun x => (weight M hζ (lmb r) x : K)) * _ = 0
    rw [← weight_diagonal M hζ lmb r]
    exact WeightedProjection.conjugate_annihilate B _ _ _
      (diagonal_inv M hζ lmb (lamp (H := H) M) r) (diagonal_inv' M hζ lmb (lamp (H := H) M) r) ell (hright s)
lemma rank_bound
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    {I : Type contextUniverse3}
    [contextInstance3 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    [Fintype.{contextUniverse3} I]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance3)) ζ M)
    {R : Type contextUniverse4}
    [Fintype.{contextUniverse4} R]
    (B : Matrix.{contextUniverse2, contextUniverse3, contextUniverse1} H I K)
    (lmb : R → @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
    (hinj : Function.Injective (fun a : R × H => shift M a.2 (lmb a.1)))
    (hN : ∀ r, (WeightedProjection.gram B (weights M hζ lmb r)).det ≠ 0) :
    Fintype.card R * Fintype.card I * Fintype.card H ≤
      Module.finrank K (LinearMap.range (Algebra.lmul K _ (element M hζ B lmb))) := by
  let C (r : R) := (WeightedProjection.gram B (weights M hζ lmb r))⁻¹ * B.transpose * Matrix.diagonal (weights M hζ lmb r)
  have hCB (r : R) : C r * B = 1 := by
    change (WeightedProjection.gram B _)⁻¹ * B.transpose * Matrix.diagonal _ * B = 1
    simpa only [WeightedProjection.gram,Matrix.mul_assoc] using
      Matrix.nonsing_inv_mul (WeightedProjection.gram B (weights M hζ lmb r)) (isUnit_iff_ne_zero.mpr (hN r))
  have hd := MatrixUnits.regular_rank_bound (freeUnit M hζ lmb) (freeUnit_mul M hζ hc lmb hinj)
    (freeUnit_independent M hζ hc lmb hinj) B C hCB
  have heq : (fun r => B*C r) = projection M hζ B lmb := by
    funext r
    simp only [C,projection,WeightedProjection.projection,Matrix.mul_assoc]
  rw [heq] at hd
  exact hd
end Blocks

end
end OddKaplansky.WreathFourier

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.Augmentation
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {E : Type portUniverse2} [Field K] [sectionInstance28 : Fintype E] [DecidableEq E]
variable (p : ℕ) [sectionInstance30 : Fact p.Prime] [sectionInstance29 : CharP K p]
abbrev C := Multiplicative (E → ZMod p)
abbrev R := MonoidAlgebra K (C (E := E) p)

def coordinate (i : E) : C (E := E) p := Multiplicative.ofAdd (Pi.single i 1)
def delta (x : E → ZMod p) : R (K := K) (E := E) p := MonoidAlgebra.single (Multiplicative.ofAdd x) 1
def X (i : E) : R (K := K) (E := E) p := delta p (Pi.single i 1) - 1

lemma coordinate_pow
    {E : Type contextUniverse1}
    [Fintype.{contextUniverse1} E]
    [DecidableEq.{contextUniverse1 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)] (i : E) : coordinate p i ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  ext j
  simp [coordinate, Pi.single_apply, apply_ite]

instance : CharP (R (K := K) (E := E) p) p :=
  CharP.of_ringHom_of_ne_zero (algebraMap K _) p (Fact.out : p.Prime).ne_zero

lemma X_pow (i : E) : X (K := K) p i ^ p = 0 := by
  rw [X, sub_pow_char, one_pow]
  have he : delta (K := K) p (Pi.single i (1 : ZMod p)) ^ p = 1 := by
    change (MonoidAlgebra.of K (C (E := E) p) (coordinate p i)) ^ p = 1
    rw [← map_pow, coordinate_pow, map_one]
  rw [he, sub_self]

lemma delta_product
    {K : Type contextUniverse1}
    {E : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} E]
    [DecidableEq.{contextUniverse2 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p] (x : E → ZMod p) :
    delta (K := K) p x = ∏ i, (1 + X p i) ^ (x i).val := by
  have he : Multiplicative.ofAdd x = ∏ i, coordinate p i ^ (x i).val := by
    apply Multiplicative.toAdd.injective
    ext j
    simp only [toAdd_prod, toAdd_pow, coordinate, toAdd_ofAdd,
      Finset.sum_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, Pi.single_apply,
      mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ZMod.natCast_zmod_val]
  calc
    delta p x = MonoidAlgebra.of K _ (∏ i, coordinate p i ^ (x i).val) := congrArg _ he
    _ = ∏ i, (MonoidAlgebra.of K _ (coordinate p i)) ^ (x i).val := by simp only [map_prod, map_pow]
    _ = _ := by apply Finset.prod_congr rfl; intro i _; congr 1; simp only [coordinate, MonoidAlgebra.of_apply, X, delta, add_sub_cancel]

open MvPolynomial in
def shiftPolynomial (x : E → ZMod p) : MvPolynomial E K := ∏ i : E, (1 + MvPolynomial.X i) ^ (x i).val

def eval : MvPolynomial E K →ₐ[K] R (K := K) (E := E) p := MvPolynomial.aeval (X p)

lemma eval_shiftPolynomial (x : E → ZMod p) : eval p (shiftPolynomial (K := K) p x) = delta p x := by
  rw [shiftPolynomial, map_prod]
  simp only [map_pow, map_add, map_one, eval, MvPolynomial.aeval_X]
  exact (delta_product p x).symm

lemma degreeOf_shiftPolynomial
    {K : Type contextUniverse1}
    {E : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} E]
    [DecidableEq.{contextUniverse2 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p] (x : E → ZMod p) (i : E) :
    (shiftPolynomial (K := K) p x).degreeOf i ≤ (x i).val := by
  unfold shiftPolynomial
  apply (MvPolynomial.degreeOf_prod_le _ _ _).trans
  calc
    _ ≤ ∑ j : E, (if i = j then 1 else 0) * (x j).val := by
      apply Finset.sum_le_sum
      intro j _
      apply (MvPolynomial.degreeOf_pow_le _ _ _).trans
      rw [Nat.mul_comm (x j).val]
      apply Nat.mul_le_mul_right
      apply (MvPolynomial.degreeOf_add_le _ _ _).trans
      by_cases hij : i = j <;> simp only [hij, MvPolynomial.degreeOf_one, MvPolynomial.degreeOf_X_self, zero_le, sup_of_le_right, ↓reduceIte, Std.le_refl, ne_eq, not_false_eq_true, MvPolynomial.degreeOf_X_of_ne, max_self]
    _ = (x i).val := by simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

def monomial (n : E → Fin p) : R (K := K) (E := E) p := ∏ i, X p i ^ (n i).val

def monomialSpan : Submodule K (R (K := K) (E := E) p) := Submodule.span K (Set.range (monomial p))

lemma eval_mem_span
    {K : Type contextUniverse1}
    {E : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} E]
    [DecidableEq.{contextUniverse2 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p] (f : MvPolynomial E K) (hf : ∀ i, f.degreeOf i < p) :
    eval p f ∈ monomialSpan (K := K) p := by
  rw [f.as_sum, map_sum]
  apply Submodule.sum_mem
  intro d hd
  have hb (i : E) : d i < p := (MvPolynomial.monomial_le_degreeOf i hd).trans_lt (hf i)
  let n : E → Fin p := fun i => ⟨d i, hb i⟩
  have he : eval p (MvPolynomial.monomial d (f.coeff d)) = f.coeff d • monomial p n := by
    simp only [eval, MvPolynomial.aeval_monomial, monomial, n, Algebra.smul_def]
    congr 1
    exact Finsupp.prod_fintype _ _ (by simp only [pow_zero, implies_true])
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n,rfl⟩)

lemma span_eq_top : monomialSpan (K := K) (E := E) p = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  induction z using MonoidAlgebra.induction_on with
  | of g =>
    change delta p g.toAdd ∈ _
    rw [← eval_shiftPolynomial]
    apply eval_mem_span
    intro i
    exact (degreeOf_shiftPolynomial p g.toAdd i).trans_lt (ZMod.val_lt _)
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | smul c x hx => exact Submodule.smul_mem _ c hx

end
end OddKaplansky.Augmentation

namespace OddKaplansky.Augmentation
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse3} {E : Type portUniverse4} [Field K] [Fintype E] [DecidableEq E]
variable (p : ℕ) [Fact p.Prime] [CharP K p]

lemma monomial_independent : LinearIndependent K (monomial (K := K) (E := E) p) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · exact (span_eq_top p).ge
  · rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis (C (E := E) p) K)]
    simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ, C, Fintype.card_multiplicative, ZMod.card]

def gridBasis : Module.Basis (E → Fin p) K (R (K := K) (E := E) p) :=
  Module.Basis.mk (monomial_independent p) (span_eq_top p).ge
@[simp] lemma gridBasis_apply (n : E → Fin p) : gridBasis (K := K) p n = monomial p n :=
  Module.Basis.mk_apply _ _ _

lemma eval_zero_of_high_degree (f : MvPolynomial E K)
    (hf : ∀ d ∈ f.support, Fintype.card E * (p-1) < Finsupp.degree d) :
    eval p f = 0 := by
  rw [f.as_sum, map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  have hi : ∃ i : E, p ≤ d i := by
    by_contra! hn
    have hle : Finsupp.degree d ≤ Fintype.card E * (p-1) := by
      change d.sum (fun _ n => n) ≤ _
      rw [Finsupp.sum_fintype _ _ (by simp only [implies_true])]
      calc
        _ ≤ ∑ _i : E, (p-1) := Finset.sum_le_sum (fun i _ => by have := hn i; omega)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    exact (hf d hd).not_ge hle
  obtain ⟨i,hi⟩ := hi
  rw [eval, MvPolynomial.aeval_monomial]
  have hz : d.prod (fun i k => X (K := K) p i ^ k) = 0 := by
    rw [Finsupp.prod_fintype _ _ (by simp only [pow_zero, implies_true])]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact pow_eq_zero_of_le hi (X_pow p i)
  rw [hz, mul_zero]

lemma eval_ideal_power (n : ℕ) (hn : Fintype.card E * (p-1) < n)
    (f : MvPolynomial E K) (hf : f ∈ MvPolynomial.idealOfVars E K ^ n) : eval p f = 0 := by
  apply eval_zero_of_high_degree
  intro d hd
  exact hn.trans_le ((MvPolynomial.mem_pow_idealOfVars_iff n f).mp hf d hd)

end
end OddKaplansky.Augmentation

namespace OddKaplansky.Augmentation
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse5} {E : Type portUniverse6} [Field K] [Fintype E] [sectionInstance31 : DecidableEq E]
variable (p : ℕ) [sectionInstance32 : Fact p.Prime] [sectionInstance33 : CharP K p]

def exponents (n : E → Fin p) : E →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (n i).val)
@[simp] lemma exponents_apply
    {E : Type contextUniverse1}
    [Fintype.{contextUniverse1} E]
    [DecidableEq.{contextUniverse1 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)] (n : E → Fin p) (i : E) : exponents p n i = (n i).val := rfl
lemma degree_exponents
    {E : Type contextUniverse1}
    [Fintype.{contextUniverse1} E]
    [DecidableEq.{contextUniverse1 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)] (n : E → Fin p) : Finsupp.degree (exponents p n) = ∑ i, (n i).val := by
  change (exponents p n).sum (fun _ a => a) = _
  rw [Finsupp.sum_fintype _ _ (by simp only [implies_true])]
  rfl
lemma eval_monomial
    {K : Type contextUniverse1}
    {E : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} E]
    [DecidableEq.{contextUniverse2 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p] (n : E → Fin p) :
    eval (K := K) p (MvPolynomial.monomial (exponents p n) 1) = monomial p n := by
  rw [eval, MvPolynomial.aeval_monomial, map_one, one_mul]
  exact Finsupp.prod_fintype _ _ (by simp only [pow_zero, implies_true])

lemma shiftPolynomial_sub_one_mem
    {K : Type contextUniverse1}
    {E : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} E]
    [DecidableEq.{contextUniverse2 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p] (x : E → ZMod p) :
    shiftPolynomial (K := K) p x - 1 ∈ MvPolynomial.idealOfVars E K := by
  let I := MvPolynomial.idealOfVars E K
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  change Ideal.Quotient.mk I (_ - 1) = 0
  rw [map_sub, map_one, shiftPolynomial, map_prod]
  have hx (i : E) : Ideal.Quotient.mk I (MvPolynomial.X i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
  simp only [map_pow, map_add, map_one, hx, add_zero, one_pow, Finset.prod_const_one, sub_self]

lemma annihilates_monomial (x : E → ZMod p) (n : E → Fin p) (ell : ℕ)
    (hn : Fintype.card E * (p-1) < ell + ∑ i, (n i).val) :
    (delta (K := K) p x - 1)^ell * monomial p n = 0 := by
  have hpow := Ideal.pow_mem_pow (shiftPolynomial_sub_one_mem (K := K) p x) ell
  have hmon : MvPolynomial.monomial (exponents p n) (1 : K) ∈
      MvPolynomial.idealOfVars E K ^ (∑ i, (n i).val) := by
    apply (MvPolynomial.monomial_mem_pow_idealOfVars_iff _ _ one_ne_zero).mpr
    rw [degree_exponents]
  have hmul : (shiftPolynomial (K := K) p x - 1)^ell * MvPolynomial.monomial (exponents p n) 1 ∈
      MvPolynomial.idealOfVars E K ^ (ell + ∑ i, (n i).val) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hpow hmon
  have he := eval_ideal_power p _ hn _ hmul
  simpa only [map_mul, map_pow, map_sub, map_one, eval_shiftPolynomial, eval_monomial] using he

end
end OddKaplansky.Augmentation

end

end OAI
end

section
namespace OAI



section

namespace OddKaplansky.Augmentation
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {E : Type portUniverse2} [Field K] [sectionInstance34 : Fintype E] [sectionInstance35 : DecidableEq E]
variable (p : ℕ) [sectionInstance36 : Fact p.Prime] [sectionInstance37 : CharP K p]

abbrev High (ell : ℕ) := {n : E → Fin p // Fintype.card E * (p-1) < ell + ∑ i, (n i).val}

def columns (ell : ℕ) : Matrix (C (E := E) p) (High (E := E) p ell) K :=
  fun x n => (monomial p n.val).coeff x

def regular : R (K := K) (E := E) p →ₐ[K] Matrix (C (E := E) p) (C (E := E) p) K :=
  Algebra.leftMulMatrix (MonoidAlgebra.basis _ K)

lemma basis_repr
    {K : Type contextUniverse1}
    {E : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} E]
    [DecidableEq.{contextUniverse2 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p] (z : R (K := K) (E := E) p) :
    (MonoidAlgebra.basis (C (E := E) p) K).repr z = z.coeff := rfl

lemma regular_delta
    {K : Type contextUniverse1}
    {E : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} E]
    [DecidableEq.{contextUniverse2 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p] (s : E → ZMod p) (x y : C (E := E) p) :
    regular (K := K) p (delta p s) x y = if x.toAdd = s + y.toAdd then 1 else 0 := by
  rw [regular, Algebra.leftMulMatrix_eq_repr_mul]
  simp only [MonoidAlgebra.basis_apply, delta, MonoidAlgebra.single_mul_single, one_mul,
    basis_repr, MonoidAlgebra.coeff_single]
  simp only [Finsupp.single_apply, eq_comm]
  rfl

lemma regular_mul_vec
    {K : Type contextUniverse1}
    {E : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} E]
    [DecidableEq.{contextUniverse2 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p] (z t : R (K := K) (E := E) p) :
    regular p z *ᵥ (fun x => t.coeff x) = fun x => (z*t).coeff x := by
  have h := Algebra.leftMulMatrix_mulVec_repr (MonoidAlgebra.basis (C (E := E) p) K) z t
  simpa only [regular, basis_repr] using h

lemma columns_independent (ell : ℕ) : LinearIndependent K (columns (K := K) (E := E) p ell).col := by
  let L : R (K := K) (E := E) p ≃ₗ[K] (C (E := E) p → K) :=
    (MonoidAlgebra.coeffLinearEquiv K).trans (Finsupp.linearEquivFunOnFinite K K (C p))
  have h := ((monomial_independent (K := K) (E := E) p).comp (fun n : High (E := E) p ell => n.val) Subtype.val_injective).map' L.toLinearMap L.ker
  exact h

lemma columns_annihilated (ell : ℕ) (s : E → ZMod p) :
    (regular (K := K) p (delta p s) - 1)^ell * columns (K := K) (E := E) p ell = 0 := by
  have he : (regular (K := K) p (delta p s) - 1)^ell = regular p ((delta p s - 1)^ell) := by simp only [map_pow, map_sub, map_one]
  rw [he]
  ext x n
  change (regular p ((delta p s - 1)^ell) *ᵥ (fun x => (monomial p n.val).coeff x)) x = 0
  rw [regular_mul_vec, annihilates_monomial p s n.val ell n.property]
  rfl

lemma regular_delta_transpose (s : E → ZMod p) :
    (regular (K := K) p (delta p s)).transpose = regular p (delta p (-s)) := by
  ext x y
  simp only [Matrix.transpose_apply,regular_delta]
  congr 1
  apply propext
  constructor
  · intro h; rw [h]; simp only [neg_add_cancel_left]
  · intro h; rw [h]; simp only [add_neg_cancel_left]

lemma columns_transpose_annihilated (ell : ℕ) (s : E → ZMod p) :
    (columns (K := K) (E := E) p ell).transpose * (regular (K := K) (E := E) p (delta p s)-(1 : Matrix (C p) (C p) K))^ell = 0 := by
  have h := congrArg Matrix.transpose (columns_annihilated (K := K) (E := E) p ell (-s))
  simpa only [Matrix.transpose_mul, Matrix.transpose_pow, Matrix.transpose_sub,
    Matrix.transpose_one, regular_delta_transpose, neg_neg, Matrix.transpose_zero] using h

end
end OddKaplansky.Augmentation

end

end OAI
end

section
namespace OAI

section
namespace OddKaplansky.SimplexCount
noncomputable section
open scoped Classical BigOperators

abbrev Triangle (ell : ℕ) := Σ a : Fin ell, Fin (ell-a.val)
abbrev Tetrahedron (ell : ℕ) := Σ a : Fin ell, Triangle (ell-a.val)

lemma card_triangle_succ (ell : ℕ) : Fintype.card (Triangle (ell+1)) = ell+1+Fintype.card (Triangle ell) := by
  simp only [Triangle, Fintype.card_sigma, Fintype.card_fin, Fin.sum_univ_succ,
    Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.add_sub_add_right]
lemma card_tetrahedron_succ (ell : ℕ) : Fintype.card (Tetrahedron (ell+1)) =
    Fintype.card (Triangle (ell+1))+Fintype.card (Tetrahedron ell) := by
  conv_lhs => rw [Fintype.card_sigma]
  conv_rhs => arg 2; rw [Fintype.card_sigma]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.add_sub_add_right]
  rfl

lemma card_triangle (ell : ℕ) : Fintype.card (Triangle ell) = (ell+1).choose 2 := by
  induction ell with
  | zero => simp only [Triangle, zero_tsub, Fintype.card_eq_zero, zero_add, Nat.choose_succ_self]
  | succ ell ih =>
    rw [card_triangle_succ,ih]
    simpa only [add_comm, Nat.choose_one_right, Nat.succ_eq_add_one, Nat.reduceAdd] using (Nat.choose_succ_succ (ell+1) 1).symm
lemma card_tetrahedron (ell : ℕ) : Fintype.card (Tetrahedron ell) = (ell+2).choose 3 := by
  induction ell with
  | zero => simp only [Tetrahedron, zero_tsub, Fintype.card_eq_zero, zero_add, Nat.choose_succ_self]
  | succ ell ih =>
    rw [card_tetrahedron_succ,card_triangle,ih]
    simpa only [add_comm, add_left_comm, Nat.reduceAdd, add_assoc, Nat.succ_eq_add_one] using (Nat.choose_succ_succ (ell+2) 2).symm

abbrev Deficit (p ell : ℕ) := {a : Fin 3 → Fin p // ∑ i, (a i).val < ell}

def deficitEquiv (p ell : ℕ) (hl : ell ≤ p) : Deficit p ell ≃ Tetrahedron ell where
  toFun a := by
    have ha := a.property
    simp only [Fin.sum_univ_succ, Fin.isValue, Fin.succ_zero_eq_one, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_one_eq_two] at ha
    refine ⟨⟨(a.val 0).val, by omega⟩, ⟨⟨(a.val 1).val, ?_⟩, ⟨(a.val 2).val, ?_⟩⟩⟩
    · change (a.val 1).val < ell - (a.val 0).val
      omega
    · change (a.val 2).val < ell - (a.val 0).val - (a.val 1).val
      omega
  invFun a := ⟨![⟨a.1.val, a.1.isLt.trans_le hl⟩,
    ⟨a.2.1.val, by have := a.2.1.isLt; omega⟩,
    ⟨a.2.2.val, by have := a.2.2.isLt; omega⟩],by
      have := a.1.isLt; have := a.2.1.isLt; have := a.2.2.isLt
      simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
        Matrix.cons_val_fin_one,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
      omega⟩
  left_inv a := by ext i; fin_cases i <;> rfl
  right_inv a := by rcases a with ⟨a,b,c⟩; rfl

lemma card_deficit (p ell : ℕ) (hl : ell ≤ p) : Fintype.card (Deficit p ell) = (ell+2).choose 3 := by
  rw [Fintype.card_congr (deficitEquiv p ell hl),card_tetrahedron]

lemma twice_triangle (ell : ℕ) : 2*Fintype.card (Triangle ell) = ell*(ell+1) := by
  induction ell with
  | zero => simp only [Triangle, zero_tsub, Fintype.card_eq_zero, mul_zero, zero_add, mul_one]
  | succ ell ih => rw [card_triangle_succ]; first | linarith only [ih] | nlinarith
lemma six_tetrahedron (ell : ℕ) : 6*Fintype.card (Tetrahedron ell) = ell*(ell+1)*(ell+2) := by
  induction ell with
  | zero => simp only [Tetrahedron, zero_tsub, Fintype.card_eq_zero, mul_zero, zero_add, mul_one, zero_mul]
  | succ ell ih =>
    rw [card_tetrahedron_succ]
    have h := twice_triangle (ell+1)
    first | linarith only [ih, h] | nlinarith

end
end OddKaplansky.SimplexCount

end

end OAI
end

section
namespace OAI

section

namespace OddKaplansky.Augmentation
noncomputable section
open scoped Classical BigOperators
variable (p ell : ℕ) [sectionInstance38 : Fact p.Prime]

lemma complement_lt
    (p : Nat)
    [Fact (Nat.Prime p)] (n : Fin p) : p-1-n.val < p := by have := n.isLt; omega
lemma complement_complement
    (p : Nat)
    [Fact (Nat.Prime p)] (n : Fin p) : p-1-(p-1-n.val) = n.val := by have := n.isLt; omega

def highEquivDeficit : High (E := Fin 3) p ell ≃ SimplexCount.Deficit p ell where
  toFun n := ⟨fun i => ⟨p-1-(n.val i).val, complement_lt p (n.val i)⟩,by
    have hn := n.property
    have h0 := (n.val 0).isLt; have h1 := (n.val 1).isLt; have h2 := (n.val 2).isLt
    simp only [Fintype.card_fin, Fin.sum_univ_succ, Fin.isValue, Fin.succ_zero_eq_one, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_one_eq_two, gt_iff_lt] at hn ⊢
    omega⟩
  invFun n := ⟨fun i => ⟨p-1-(n.val i).val, complement_lt p (n.val i)⟩,by
    have hn := n.property
    have h0 := (n.val 0).isLt; have h1 := (n.val 1).isLt; have h2 := (n.val 2).isLt
    simp only [Fin.sum_univ_succ, Fin.isValue, Fin.succ_zero_eq_one, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_one_eq_two, Fintype.card_fin, gt_iff_lt] at hn ⊢
    omega⟩
  left_inv n := by ext i; exact complement_complement p (n.val i)
  right_inv n := by ext i; exact complement_complement p (n.val i)

lemma card_high (hl : ell ≤ p) : Fintype.card (High (E := Fin 3) p ell) = (ell+2).choose 3 := by
  rw [Fintype.card_congr (highEquivDeficit p ell),SimplexCount.card_deficit p ell hl]

lemma card_high_le
    (p : Nat)
    (ell : Nat)
    [Fact (Nat.Prime p)] : Fintype.card (High (E := Fin 3) p ell) ≤ p^3 := by
  calc
    _ ≤ Fintype.card (Fin 3 → Fin p) := Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = _ := by simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ]

lemma high_ratio (hp : p = 2*ell+1) (hl : 1 ≤ ell) :
    p^3 < 48*Fintype.card (High (E := Fin 3) p ell) := by
  have he : ell ≤ p := by omega
  rw [card_high p ell he, ← SimplexCount.card_tetrahedron]
  have hc := SimplexCount.six_tetrahedron ell
  rw [hp]
  first | linarith only [hc, hl, Nat.mul_le_mul hl hl] | nlinarith

end
end OddKaplansky.Augmentation

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.Augmentation
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {E : Type portUniverse2} [Field K] [Fintype E] [DecidableEq E]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
lemma regular_translation (s : C (E := E) p) :
    regular (K := K) p (delta p s.toAdd) = TranslationMatrix.matrix s := by
  ext x y
  simp only [regular_delta,TranslationMatrix.matrix]
  congr 1
end
end OddKaplansky.Augmentation

namespace OddKaplansky.ModularSource
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse3} [Field K] [sectionInstance39 : Fintype K]
variable (p M ell : ℕ) [sectionInstance40 : Fact p.Prime] [sectionInstance41 : NeZero M] [CharP K p]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ M)
abbrev P := Multiplicative (Fin 3 → ZMod p)
lemma card_P : Fintype.card (P p) = p^3 := by simp only [P, Fintype.card_multiplicative, Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
lemma base_nonzero
    {K : Type contextUniverse1}
    [contextInstance1 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse1} K]
    (p : Nat)
    (M : Nat)
    [Fact (Nat.Prime p)]
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance1))))
  p] (hM : M+1=p^4) : (Fintype.card (WreathFourier.Base (H := P p) M) : K) ≠ 0 := by
  have hm : (M : K) ≠ 0 := by
    have hc := congrArg (fun n : ℕ => (n : K)) hM
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_pow,CharP.cast_eq_zero K p,zero_pow (by omega : 4≠0)] at hc
    intro hz
    rw [hz,zero_add] at hc
    exact one_ne_zero hc
  have hcard : Fintype.card (WreathFourier.Base (H := P p) M) = M^(p^3) := by simp only [WreathFourier.Base, Fourier.C, Fintype.card_pi, Fintype.card_multiplicative, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hcard,Nat.cast_pow]
  exact pow_ne_zero _ hm
lemma quartic_large
    (p : Nat)
    (M : Nat)
    [Fact (Nat.Prime p)]
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (hp : 5 ≤ p) (hM : M+1=p^4) : 4*p^3 < M := by
  have h1 : 2 ≤ p^3 := by have hh := Nat.pow_le_pow_left hp 3; norm_num at hh; omega
  have h2 := Nat.mul_le_mul_right (p^3) hp
  first | linarith only [hM, h1, h2, show p^4=p*p^3 by ring] | nlinarith [show p^4=p*p^3 by ring]
lemma left_ann
    {K : Type contextUniverse1}
    [contextInstance1 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse1} K]
    (p : Nat)
    (ell : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance1))))
  p]
    : ∀ s : P p, (TranslationMatrix.matrix (K := K) s - 1)^ell * Augmentation.columns (K := K) (E := Fin 3) p ell = 0 := by
  intro s
  rw [← Augmentation.regular_translation (K := K) p s]
  exact Augmentation.columns_annihilated p ell s.toAdd
lemma right_ann
    {K : Type contextUniverse1}
    [contextInstance1 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse1} K]
    (p : Nat)
    (ell : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance1))))
  p]
    : ∀ s : P p, (Augmentation.columns (K := K) (E := Fin 3) p ell).transpose * (TranslationMatrix.matrix (K := K) s - 1)^ell = 0 := by
  intro s
  rw [← Augmentation.regular_translation (K := K) p s]
  exact Augmentation.columns_transpose_annihilated p ell s.toAdd
lemma high_small (hp : 5≤p) (hM : M+1=p^4) : 4*Fintype.card (Augmentation.High (E := Fin 3) p ell) < M := by
  have hh := Augmentation.card_high_le p ell
  have hm := quartic_large p M hp hM
  omega
lemma point_small (hp : 5≤p) (hM : M+1=p^4) : 4*(Fintype.card (P p)-1)<M := by
  rw [card_P]
  have hm := quartic_large p M hp hM
  omega
lemma high_large (hp : 5≤p) (he : p=2*ell+1) : Fintype.card (P p) < 48*Fintype.card (Augmentation.High (E := Fin 3) p ell) := by
  rw [card_P]
  exact Augmentation.high_ratio p ell he (by omega)
end
end OddKaplansky.ModularSource

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.SourceOrders
noncomputable section
open scoped Classical
@[instance_reducible]
def cyclic (M : ℕ) [NeZero M] : LinearOrder (Fourier.C M) :=
  @FiniteChoice.multiplicativeOrder (ZMod M) (FiniteChoice.residueOrder M)
@[instance_reducible]
def point (p : ℕ) [NeZero p] : LinearOrder (Multiplicative (Fin 3 → ZMod p)) :=
  @FiniteChoice.multiplicativeOrder (Fin 3 → ZMod p)
    (@FiniteChoice.functionOrder (Fin 3) (ZMod p) inferInstance inferInstance (FiniteChoice.residueOrder p))
@[instance_reducible]
def character (p M : ℕ) [NeZero p] [NeZero M] :
    LinearOrder (WreathFourier.Base (H := Multiplicative (Fin 3 → ZMod p)) M) :=
  @FiniteChoice.functionOrder _ _ inferInstance (point p) (cyclic M)
end
end OddKaplansky.SourceOrders

namespace OddKaplansky.OrbitSelection.Ordered
noncomputable section
open scoped Classical BigOperators
variable {H : Type portUniverse1} {A : Type portUniverse2} [Group H] [sectionInstance42 : Fintype H] [Fintype A] [MulAction H A]
variable (order : LinearOrder A) (good : A → Prop)
def representative (r : Rep (H := H) good) : A :=
  @FiniteChoice.first A inferInstance order
    (fun a : A => (Quotient.mk'' a : MulAction.orbitRel.Quotient H A)=r.val ∧ good a) r.property
lemma representative_spec
    {H : Type contextUniverse1}
    {A : Type contextUniverse2}
    [contextInstance2 : Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    [Fintype.{contextUniverse2} A]
    [@MulAction.{contextUniverse1, contextUniverse2} H A (@DivInvMonoid.toMonoid.{contextUniverse1} H (@Group.toDivInvMonoid.{contextUniverse1} H contextInstance2))]
    (order : LinearOrder.{contextUniverse2} A)
    (good : A → Prop) (r : Rep (H := H) good) :
    (Quotient.mk'' (representative order good r) : MulAction.orbitRel.Quotient H A) = r.val ∧ good (representative order good r) := by
  exact @FiniteChoice.first_spec A inferInstance order
    (fun a : A => (Quotient.mk'' a : MulAction.orbitRel.Quotient H A)=r.val ∧ good a) r.property
lemma orbit_injective (hfree : ∀ a, good a → ∀ g : H, g • a = a → g = 1) :
    Function.Injective (fun r : Rep (H := H) good × H => r.2 • representative order good r.1) := by
  rintro ⟨r,g⟩ ⟨s,h⟩ he
  have hrs : r = s := by
    apply Subtype.ext
    have hh := congrArg (Quotient.mk'' : A → MulAction.orbitRel.Quotient H A) he
    simpa only [MulAction.orbitRel.Quotient.quotient_smul_eq,(representative_spec order good r).1,(representative_spec order good s).1] using hh
  subst s
  have hh : h⁻¹*g = 1 := by
    apply hfree (representative order good r) (representative_spec order good r).2
    simpa only [mul_smul,inv_smul_smul] using congrArg (fun a : A => h⁻¹ • a) he
  have hgh : g = h := (inv_mul_eq_one.mp hh).symm
  subst g
  rfl
end
end OddKaplansky.OrbitSelection.Ordered

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse3} {H : Type portUniverse4} {I : Type portUniverse5} [Field K] [Fintype K] [Group H] [Fintype H] [Fintype I]
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (order : LinearOrder (Base (H := H) M)) (B : Matrix H I K)

def modularElement : MonoidAlgebra K (Wreath (H := H) M) := by
  letI : MulAction H (Base (H := H) M) := shiftAction M
  exact Blocks.element M hζ B (OrbitSelection.Ordered.representative (H := H) order (Admissible M hζ B))
lemma modularElement_properties (hM : Fintype.card Kˣ = M)
    (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0) (hB : LinearIndependent K B.col)
    (ell : ℕ) (hleft : ∀ s : H, (TranslationMatrix.matrix (K := K) s - 1)^ell * B = 0)
    (hright : ∀ s : H, B.transpose * (TranslationMatrix.matrix (K := K) s - 1)^ell = 0)
    (hI : 4 * Fintype.card I < M) (hH : 4 * (Fintype.card H - 1) < M)
    (hlarge : Fintype.card H < 48 * Fintype.card I) :
    modularElement M hζ order B*modularElement M hζ order B=modularElement M hζ order B ∧
      (∀ s : H, (topElt M s-1)^ell*modularElement M hζ order B=0 ∧
        modularElement M hζ order B*(baseElt M (lamp (H := H) M)*topElt M s*baseElt M (lamp (H := H) M)⁻¹-1)^ell=0) ∧
      Fintype.card (Wreath (H := H) M) < 96 * Module.finrank K (LinearMap.range (Algebra.lmul K _ (modularElement M hζ order B))) := by
  let : MulAction H (Base (H := H) M) := shiftAction M
  let R := OrbitSelection.Rep (H := H) (Admissible M hζ B)
  let lmb : R → Base (H := H) M := OrbitSelection.Ordered.representative (H := H) order (Admissible M hζ B)
  have hlmb (r : R) : Admissible M hζ B (lmb r) := (OrbitSelection.Ordered.representative_spec order (Admissible M hζ B) r).2
  have hinj : Function.Injective (fun a : R × H => shift M a.2 (lmb a.1)) := by
    apply OrbitSelection.Ordered.orbit_injective order (Admissible M hζ B)
    intro a ha g hga
    exact ha.1 g (congrFun hga)
  have hN (r : R) : (WeightedProjection.gram B (Blocks.weights M hζ lmb r)).det ≠ 0 := (hlmb r).2
  change Blocks.element M hζ B lmb*Blocks.element M hζ B lmb=Blocks.element M hζ B lmb ∧ _
  refine ⟨Blocks.idempotent M hζ B lmb hc hinj hN,Blocks.annihilate M hζ B lmb ell hleft hright,?_⟩
  have hd := Blocks.rank_bound M hζ B lmb hc hinj hN
  have ha := cardinality M hζ hM B hB hI hH
  have hb := OrbitSelection.card_good (H := H) (Admissible M hζ B)
  change Fintype.card {a // Admissible M hζ B a} ≤ Fintype.card R * Fintype.card H at hb
  have hbase : 0 < Fintype.card (Base (H := H) M) := Fintype.card_pos
  have hR : 0 < Fintype.card R := Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at hb; omega)
  have hsmall : Fintype.card (Base (H := H) M) < 96 * Fintype.card R * Fintype.card I := by
    have hh := Nat.mul_lt_mul_of_pos_left hlarge hR
    first | linarith only [ha, hb, hh] | nlinarith
  have hn : 0 < Fintype.card H := Fintype.card_pos
  have hw := Nat.mul_lt_mul_of_pos_right hsmall hn
  have hcard : Fintype.card (Wreath (H := H) M) = Fintype.card (Base (H := H) M) * Fintype.card H := by
    rw [← Fintype.card_prod]
    apply Fintype.card_congr
    exact { toFun := fun g => (g.left,g.right)
            invFun := fun z => ⟨z.1,z.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  rw [hcard]
  change Fintype.card (Base (H := H) M)*Fintype.card H<96*Module.finrank K (LinearMap.range (Algebra.lmul K _ (Blocks.element M hζ B lmb)))
  first | linarith only [hw, hd] | nlinarith
end
end OddKaplansky.WreathFourier

namespace OddKaplansky.ModularSource
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse6} [Field K] [Fintype K]
variable (p M ell : ℕ) [Fact p.Prime] [NeZero M] [CharP K p]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ M)
def explicitElement : MonoidAlgebra K (WreathFourier.Wreath (H := P p) M) :=
  WreathFourier.modularElement M hζ (SourceOrders.character p M) (Augmentation.columns (K := K) (E := Fin 3) p ell)
lemma explicit_properties (hp : 5 ≤ p) (hpell : p=2*ell+1) (hM : M+1=p^4)
    (hK : Fintype.card Kˣ = M) :
    explicitElement p M ell hζ*explicitElement p M ell hζ=explicitElement p M ell hζ ∧
      (∀ s : P p, (WreathFourier.topElt M s-1)^ell*explicitElement p M ell hζ=0 ∧
        explicitElement p M ell hζ*(WreathFourier.baseElt M (WreathFourier.lamp (H := P p) M)*WreathFourier.topElt M s*WreathFourier.baseElt M (WreathFourier.lamp (H := P p) M)⁻¹-1)^ell=0) ∧
      Fintype.card (WreathFourier.Wreath (H := P p) M) < 96 * Module.finrank K (LinearMap.range (Algebra.lmul K _ (explicitElement p M ell hζ))) := by
  apply WreathFourier.modularElement_properties M hζ (SourceOrders.character p M)
    (Augmentation.columns (K := K) (E := Fin 3) p ell) hK
    (by simpa only [Fintype.card_eq_nat_card] using base_nonzero (K := K) p M hM)
    (Augmentation.columns_independent (K := K) (E := Fin 3) p ell) ell
    (by intro s; convert left_ann (K := K) p ell s using 1 ; congr <;> exact Subsingleton.elim _ _)
    (by intro s; convert right_ann (K := K) p ell s using 1 ; congr <;> exact Subsingleton.elim _ _)
    (by simpa only [Fintype.card_eq_nat_card] using high_small p M ell hp hM)
    (by simpa only [Fintype.card_eq_nat_card] using point_small p M hp hM)
    (by simpa only [Fintype.card_eq_nat_card] using high_large p ell hp hpell)
end
end OddKaplansky.ModularSource

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.CosetCoordinates
noncomputable section
open scoped Classical BigOperators
variable {G : Type portUniverse1} [Group G] (S : Subgroup G)
def rep (q : G ⧸ S) : G := q.out
lemma rep_mk (q : G ⧸ S) : ((rep S q : G) : G ⧸ S) = q := Quotient.out_eq' q
lemma residue_mem (g : G) : (rep S (g : G ⧸ S))⁻¹*g ∈ S :=
  QuotientGroup.eq.mp (rep_mk S (g : G ⧸ S))
def residue (g : G) : S := ⟨_,residue_mem S g⟩
lemma reconstruct (g : G) : rep S (g : G ⧸ S) * residue S g = g := by simp only [residue, mul_inv_cancel_left]
lemma mk_rep_mul (q : G ⧸ S) (s : S) : ((rep S q * (s : G) : G) : G ⧸ S) = q := by
  rw [QuotientGroup.mk_mul_of_mem _ s.property,rep_mk]
lemma residue_rep_mul (q : G ⧸ S) (s : S) : residue S (rep S q * s) = s := by
  apply Subtype.ext
  simp only [residue,mk_rep_mul]
  exact inv_mul_cancel_left _ _
def equiv : G ≃ (G ⧸ S) × S where
  toFun g := ((g : G ⧸ S),residue S g)
  invFun z := rep S z.1 * z.2
  left_inv := reconstruct S
  right_inv z := by ext <;> simp only [mk_rep_mul,residue_rep_mul]
lemma equiv_symm_apply (q : G ⧸ S) (s : S) : (equiv S).symm (q,s) = rep S q * s := rfl

variable [Fintype G]
lemma sum_right_invariant {A : Type portUniverse2} [AddCommMonoid A] (a : G → A)
    (ha : ∀ (s : S) (g : G), a (g*s) = a g) :
    ∑ g : G, a g = Fintype.card S • ∑ q : G ⧸ S, a (rep S q) := by
  rw [← Equiv.sum_comp (equiv S).symm a]
  simp only [Fintype.sum_prod_type,equiv_symm_apply,ha,Finset.sum_const,Finset.card_univ,← Finset.smul_sum]
lemma sum_left_invariant {A : Type portUniverse3} [AddCommMonoid A] (a : G → A)
    (ha : ∀ (s : S) (g : G), a (s*g) = a g) :
    ∑ g : G, a g = Fintype.card S • ∑ q : G ⧸ S, a (rep S q)⁻¹ := by
  have hh := sum_right_invariant S (fun g => a g⁻¹) (fun s g => by simpa only [mul_inv_rev,Subgroup.coe_inv] using ha s⁻¹ g⁻¹)
  have hi : (∑ g : G, a g⁻¹) = ∑ g : G, a g := Equiv.sum_comp (Equiv.inv G) a
  rw [hi] at hh
  exact hh
lemma coprime_order_of_sum (M : ℕ) (a : G → ZMod M) (hsum : ∑ g, a g = 1)
    (g : G) (hfix : ∀ x, a (g*x) = a x) : Nat.Coprime (orderOf g) M := by
  have hf : ∀ (s : Subgroup.zpowers g) (x : G), a (s*x) = a x := by
    intro s x
    obtain ⟨n,hn⟩ := s.property
    rw [← hn]
    have hnat (n : ℕ) : ∀ x, a (g^n*x)=a x := by
      induction n with
      | zero => intro x; simp only [pow_zero, one_mul]
      | succ n ih => intro x; rw [pow_succ',mul_assoc,hfix,ih]
    cases n with
    | ofNat n => simpa only [Int.ofNat_eq_natCast,zpow_natCast] using hnat n x
    | negSucc n =>
      have h := hnat (n+1) ((g^(n+1))⁻¹ * x)
      simpa only [zpow_negSucc,← mul_assoc,mul_inv_cancel,one_mul] using h.symm
  have h := sum_left_invariant (Subgroup.zpowers g) a hf
  rw [hsum,Fintype.card_zpowers,nsmul_eq_mul] at h
  exact (ZMod.isUnit_iff_coprime _ _).mp (IsUnit.of_mul_eq_one _ h.symm)
lemma eq_one_of_power_and_sum (M : ℕ) (a : G → ZMod M) (hsum : ∑ g, a g = 1)
    (g : G) (hfix : ∀ x, a (g*x) = a x) (hpow : g^M=1) : g=1 :=
  orderOf_eq_one_iff.mp ((coprime_order_of_sum M a hsum g hfix).eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hpow))
end
end OddKaplansky.CosetCoordinates

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.CosetMatrix
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {G : Type portUniverse2} [Field K] [Group G] [sectionInstance43 : Fintype G] (T : Subgroup G)
abbrev D := MonoidAlgebra K T
open CosetCoordinates

def coefficients {X : Type portUniverse3} [Finite X] : MonoidAlgebra K X ≃ₗ[K] (X → K) :=
  (MonoidAlgebra.coeffLinearEquiv K).trans (Finsupp.linearEquivFunOnFinite K K X)
def unpack : ((G ⧸ T) → D (K := K) T) ≃ₗ[K] MonoidAlgebra K G :=
  (LinearEquiv.piCongrRight (fun _ : G ⧸ T => coefficients)).trans
    ((LinearEquiv.curry K K (G ⧸ T) T).symm.trans
      ((LinearEquiv.piCongrLeft K (fun _ : (G ⧸ T) × T => K) (equiv T)).symm.trans coefficients.symm))
lemma unpack_coeff (v : (G ⧸ T) → D (K := K) T) (g : G) :
    (unpack T v).coeff g = (v (g : G ⧸ T)).coeff (residue T g) := rfl

section Commutative
variable [IsMulCommutative T]
local instance cosetMatrixCommGroup : CommGroup T := { (inferInstance : Group T) with mul_comm := mul_comm' }
end Commutative
end
end OddKaplansky.CosetMatrix

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.OrbitBlock
noncomputable section
open scoped Classical BigOperators Matrix
open WreathFourier CosetCoordinates
variable {K : Type portUniverse1} {H : Type portUniverse2} [Field K] [Group H] [Fintype H]
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
variable (lmb : Base (H := H) M) (T : Subgroup H)
variable (hT : ∀ g : H, g ∈ T ↔ shift M g lmb = lmb)
section Cross
variable (mu : Base (H := H) M) (U : Subgroup H)
variable (hsep : ∀ g : H, lmb ≠ shift M g mu)
end Cross
end
end OddKaplansky.OrbitBlock

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.CharacterIdempotents
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {A : Type portUniverse2} {B : Type portUniverse3} [Field K] [Group A] [Fintype A] [Group B] [Fintype B]
lemma projector_pushed (χ : A →* Kˣ) (j : B →* A) (ψ : B →* Kˣ)
    (hc : (Fintype.card B : K) ≠ 0) :
    projector χ * pushed j ψ = if χ.comp j = ψ then projector χ else 0 := by
  rw [pushed_eq_sum,mul_smul_comm,Finset.mul_sum]
  have hh (b : B) : projector χ * MonoidAlgebra.single (j b) ((ψ b : K)⁻¹) =
      ((χ (j b) : K) * (ψ b : K)⁻¹) • projector χ := by
    rw [show MonoidAlgebra.single (j b) ((ψ b : K)⁻¹) = (ψ b : K)⁻¹ • MonoidAlgebra.single (j b) 1 by simp only [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]]
    rw [mul_smul_comm,projector_mul_single,smul_smul,mul_comm]
  simp_rw [hh]
  rw [← Finset.sum_smul,smul_smul]
  by_cases he : χ.comp j = ψ
  · rw [if_pos he]
    have hv (b : B) : χ (j b)=ψ b := DFunLike.congr_fun he b
    simp only [hv, ne_eq, Units.ne_zero, not_false_eq_true, mul_inv_cancel₀, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hc, inv_mul_cancel₀, one_smul]
  · rw [if_neg he]
    have hn : χ.comp j * ψ⁻¹ ≠ 1 := by
      intro h
      apply he
      exact mul_inv_eq_one.mp h
    have hz := sum_character_eq_zero (χ.comp j * ψ⁻¹) hn
    simpa only [smul_eq_zero, mul_eq_zero, inv_eq_zero, MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, mul_zero, zero_smul] using congrArg (fun c : K => ((Fintype.card B : K)⁻¹*c) • projector χ) hz
end
end OddKaplansky.CharacterIdempotents

namespace OddKaplansky.SectorFourier
noncomputable section
open scoped Classical BigOperators
open WreathFourier
variable {K : Type portUniverse4} {H : Type portUniverse5} [Field K] [sectionInstance45 : Group H] [sectionInstance46 : Fintype H]
variable (M : ℕ) [sectionInstance44 : NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
def constant : Fourier.C M →* Base (H := H) M where
  toFun c := fun _ => c
  map_one' := rfl
  map_mul' _ _ := rfl
def diagonal : Fourier.C M →* Wreath (H := H) M := (base M).comp (constant M)
def weight (lmb : Base (H := H) M) : ZMod M := ∑ x, (lmb x).toAdd
lemma weight_shift
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (g : H) (lmb : Base (H := H) M) : weight M (shift M g lmb) = weight M lmb :=
  Equiv.sum_comp (Equiv.mulLeft g⁻¹) (fun x : H => (lmb x).toAdd)
lemma character_constant
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance2)) ζ M) (lmb : Base (H := H) M) :
    (Fourier.character M hζ lmb).comp (constant M) = Fourier.cyclicCharacter M hζ ↔ weight M lmb=1 := by
  constructor
  · intro he
    have hh := DFunLike.congr_fun he (Multiplicative.ofAdd (1 : ZMod M))
    have hh' := Fourier.cyclicCharacter_injective M hζ hh
    have hh'' := congrArg Multiplicative.toAdd hh'
    simpa only [weight, ofAdd_sum, constant, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, mul_one, ofAdd_toAdd, toAdd_prod] using hh''
  · intro hw
    apply MonoidHom.ext
    intro c
    simp only [MonoidHom.comp_apply,Fourier.character_apply,constant,MonoidHom.coe_mk,OneHom.coe_mk,← Finset.sum_mul]
    rw [show (∑ x : H, (lmb x).toAdd)=1 from hw,one_mul,ofAdd_toAdd]
def f : MonoidAlgebra K (Wreath (H := H) M) := CharacterIdempotents.pushed (diagonal M) (Fourier.cyclicCharacter M hζ)
lemma f_eq_packet (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
    (hm : (Fintype.card (Fourier.C M) : K) ≠ 0) :
    f (H := H) M hζ = ∑ lmb : {lmb : Base (H := H) M // weight M lmb=1}, projector M hζ lmb.val := by
  have hp : ∀ lmb : Base (H := H) M, projector M hζ lmb * f M hζ =
      if weight M lmb=1 then projector M hζ lmb else 0 := by
    intro lmb
    have hh := congrArg (MonoidAlgebra.mapDomainAlgHom K K (base (H := H) M))
      (CharacterIdempotents.projector_pushed (Fourier.character M hζ lmb) (constant M) (Fourier.cyclicCharacter M hζ) hm)
    have hf : MonoidAlgebra.mapDomainAlgHom K K (base (H := H) M)
        (CharacterIdempotents.pushed (constant M) (Fourier.cyclicCharacter M hζ)) = f M hζ := by
      simp only [CharacterIdempotents.pushed,f,diagonal,MonoidAlgebra.mapDomainAlgHom_comp,AlgHom.comp_apply]
    simp only [map_mul,apply_ite,map_zero,hf,character_constant] at hh
    by_cases hw : weight M lmb=1
    · simpa only [if_pos hw,projector,CharacterIdempotents.pushed] using hh
    · simpa only [if_neg hw,projector,CharacterIdempotents.pushed] using hh
  calc
    f (H := H) M hζ = (∑ lmb : Base (H := H) M, projector M hζ lmb) * f M hζ := by rw [sum_projector M hζ hc,one_mul]
    _ = ∑ lmb : Base (H := H) M, if weight M lmb=1 then projector M hζ lmb else 0 := by simp only [Finset.sum_mul,hp]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp only [Finset.mem_filter, Finset.mem_univ, true_and, implies_true]) _
lemma diagonal_central
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (c : Fourier.C M) (g : Wreath (H := H) M) : Commute (diagonal M c) g := by
  change diagonal M c * g = g * diagonal M c
  ext x <;> simp only [diagonal, base, constant, MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply, RegularWreathProduct.mul_left, inv_one, one_mul, Pi.mul_apply, toAdd_mul, mul_comm, RegularWreathProduct.mul_right, mul_one]
end
end OddKaplansky.SectorFourier

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.SectorOrbit
noncomputable section
open scoped Classical BigOperators Matrix
open WreathFourier CosetCoordinates
variable {K : Type portUniverse1} {H : Type portUniverse2} [Field K] [Group H] [Fintype H]
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
@[instance_reducible]
def action : MulAction H (Base (H := H) M) where
  smul g a := shift M g a
  one_smul a := by change shift M 1 a=a; rw [shift_one]; rfl
  mul_smul g h a := shift_mul M g h a
local instance : MulAction H (Base (H := H) M) := action M

variable (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
end
end OddKaplansky.SectorOrbit

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.LocalAlgebra
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {T : Type portUniverse2} [Field K] [CommGroup T]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable (hT : ∀ t : T, t^p=1)
def augment : MonoidAlgebra K T →ₐ[K] K := MonoidAlgebra.lift K K T 1
lemma augment_single (t : T) (c : K) : augment (MonoidAlgebra.single t c) = c := by simp only [augment, MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one]

include hT in
lemma power_scalar (a : MonoidAlgebra K T) : a^p = algebraMap K (MonoidAlgebra K T) ((augment a)^p) := by
  let : CharP (MonoidAlgebra K T) p := CharP.of_ringHom_of_ne_zero (algebraMap K _) p (Fact.out : p.Prime).ne_zero
  induction a using MonoidAlgebra.induction_on with
  | of t => simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_pow, hT, one_pow, augment_single, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id, Function.comp_apply, id_eq]
  | add a b ha hb => rw [add_pow_char,ha,hb,map_add,add_pow_char,map_add]
  | smul c a ha =>
    rw [smul_pow,ha,map_smul]
    simp only [smul_eq_mul,mul_pow,map_mul,Algebra.smul_def]

include hT in
lemma isUnit_iff (a : MonoidAlgebra K T) : IsUnit a ↔ augment a ≠ 0 := by
  constructor
  · intro h; exact isUnit_iff_ne_zero.mp (h.map (augment (K := K) (T := T)))
  · intro h
    have hp : IsUnit (a^p) := by
      rw [power_scalar p hT]
      exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ h)).map (algebraMap K (MonoidAlgebra K T))
    exact (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp hp

end
end OddKaplansky.LocalAlgebra

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.LocalAlgebra
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {T : Type portUniverse2} [Field K] [CommGroup T]
variable (p : ℕ) [Fact p.Prime] [sectionInstance47 : CharP K p] (hT : ∀ t : T, t^p=1)
@[instance_reducible]
def exponentModule : Module (ZMod p) (Additive T) :=
  AddCommGroup.zmodModule (fun t : Additive T => congrArg Additive.ofMul (hT t.toMul))
variable [Module (ZMod p) (Additive T)]

variable {ι : Type portUniverse3} [Fintype ι]
end
end OddKaplansky.LocalAlgebra

namespace OddKaplansky.NilpotentSum
noncomputable section
open scoped Classical BigOperators
variable {R : Type portUniverse4} {ι : Type portUniverse5} [CommSemiring R]
end
end OddKaplansky.NilpotentSum

namespace OddKaplansky.LocalAlgebra
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse6} {T : Type portUniverse7} [Field K] [CommGroup T]
variable (p : ℕ) [Fact p.Prime] [CharP K p] (hT : ∀ t : T, t^p=1)
variable [Module (ZMod p) (Additive T)]
variable {ι : Type portUniverse8} [Fintype ι]
variable [sectionInstance48 : Fintype T]
end
end OddKaplansky.LocalAlgebra

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.FiniteMatrixInverse
noncomputable section
open scoped Classical BigOperators Matrix
variable {D : Type portUniverse1} {S : Type portUniverse2} [CommRing D] [Fintype S] [DecidableEq S]
end
end OddKaplansky.FiniteMatrixInverse

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.LocalAlgebra
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {T : Type portUniverse2} {S : Type portUniverse3} [Field K] [CommGroup T] [sectionInstance49 : Fintype T] [sectionInstance50 : Fintype S] [sectionInstance51 : DecidableEq S]
variable (p : ℕ) [Fact p.Prime] [CharP K p] (hT : ∀ t : T, t^p=1)
variable (j : T →* Multiplicative (Fin 3 → ZMod p)) (hj : Function.Injective j)

end
end OddKaplansky.LocalAlgebra

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.IdempotentFree
noncomputable section
open scoped Classical BigOperators
variable {D : Type portUniverse1} {V : Type portUniverse2} [CommRing D] [sectionInstance52 : IsLocalRing D] [AddCommGroup V] [Module D V]
variable (E : V →ₗ[D] V) (hE : E ∘ₗ E = E)
include hE in
omit [IsLocalRing D] in
lemma range_fixed (x : LinearMap.range E) : E x = x := by
  obtain ⟨v,hv⟩ := x.property
  have h := LinearMap.congr_fun hE v
  simpa only [LinearMap.comp_apply,hv] using h

section Rectangular
variable {W : Type portUniverse3} {N : Type portUniverse4} [sectionInstance54 : Fintype W] [sectionInstance53 : Fintype N]
variable (q : (N → V) ≃ₗ[D] (W → LinearMap.range E))
def J : Matrix W N (Module.End D V) := fun w n =>
  (LinearMap.range E).subtype ∘ₗ LinearMap.proj w ∘ₗ q.toLinearMap ∘ₗ LinearMap.single D (fun _ : N => V) n
def Y : Matrix N W (Module.End D V) := fun n w =>
  LinearMap.proj n ∘ₗ q.symm.toLinearMap ∘ₗ LinearMap.single D (fun _ : W => LinearMap.range E) w ∘ₗ E.rangeRestrict
omit [IsLocalRing D] in
lemma single_sum (x : N → V) : ∑ n : N, (LinearMap.single D (fun _ : N => V) n) (x n) = x := by
  ext n
  simp only [LinearMap.coe_single, Finset.sum_apply, Finset.sum_pi_single, Finset.mem_univ, ↓reduceIte]
omit [IsLocalRing D] in
lemma YJ
    {D : Type contextUniverse1} {V : Type contextUniverse2}
    [CommRing D] [AddCommGroup V] [Module D V]
    (E : V →ₗ[D] V) (hE : E ∘ₗ E = E)
    {W : Type contextUniverse3} {N : Type contextUniverse4} [Fintype W] [Fintype N]
    (q : (N → V) ≃ₗ[D] (W → LinearMap.range E)) : Y E q * J E q = 1 := by
  funext n n'
  apply LinearMap.ext
  intro v
  let x := q (Pi.single n' v)
  have hs : ∑ w : W, Pi.single w (x w) = x := single_sum (D := D) x
  calc
    (Y E q * J E q) n n' v = ∑ w : W, (q.symm (Pi.single w (x w))) n := by
      simp only [Matrix.mul_apply,Module.End.mul_apply,LinearMap.sum_apply,Y,J,LinearMap.comp_apply]
      apply Finset.sum_congr rfl
      intro w _
      change (q.symm (Pi.single w (E.rangeRestrict (x w : V)))) n = (q.symm (Pi.single w (x w))) n
      have hr : E.rangeRestrict (x w : V) = x w := Subtype.ext (range_fixed E hE (x w))
      rw [hr]
    _ = (q.symm (∑ w : W, Pi.single w (x w))) n := by simp only [map_sum,Finset.sum_apply]
    _ = (Pi.single n' v : N → V) n := by rw [hs]; exact congrFun (q.symm_apply_apply (Pi.single n' v)) n
    _ = (1 : Matrix N N (Module.End D V)) n n' v := by
      by_cases h : n=n'
      · subst n'; simp only [Pi.single_eq_same, Matrix.one_apply_eq, Module.End.one_apply]
      · simp only [ne_eq, h, not_false_eq_true, Pi.single_eq_of_ne, Matrix.one_apply_ne, LinearMap.zero_apply]
omit [IsLocalRing D] in
lemma JY
    {D : Type contextUniverse1} {V : Type contextUniverse2}
    [CommRing D] [AddCommGroup V] [Module D V]
    (E : V →ₗ[D] V)
    {W : Type contextUniverse3} {N : Type contextUniverse4} [Fintype W] [Fintype N]
    (q : (N → V) ≃ₗ[D] (W → LinearMap.range E)) : J E q * Y E q = Matrix.diagonal (fun _ : W => E) := by
  funext w w'
  apply LinearMap.ext
  intro v
  let x := q.symm (Pi.single w' (E.rangeRestrict v))
  have hs : ∑ n : N, Pi.single n (x n) = x := single_sum (D := D) x
  calc
    (J E q * Y E q) w w' v = ∑ n : N, ((q (Pi.single n (x n))) w : V) := by
      simp only [Matrix.mul_apply,Module.End.mul_apply,LinearMap.sum_apply,Y,J,LinearMap.comp_apply]
      rfl
    _ = ((q (∑ n : N, Pi.single n (x n))) w : V) := by simp only [map_sum,Finset.sum_apply,Submodule.coe_sum]
    _ = (((Pi.single w' (E.rangeRestrict v) : W → LinearMap.range E)) w : V) := by rw [hs]; exact congrArg (fun f : W → LinearMap.range E => (f w : V)) (q.apply_symm_apply (Pi.single w' (E.rangeRestrict v)))
    _ = (Matrix.diagonal (fun _ : W => E)) w w' v := by
      by_cases h : w=w'
      · subst w'; simp only [Pi.single_eq_same, LinearMap.codRestrict_apply, Matrix.diagonal_apply_eq]
      · simp only [ne_eq, h, not_false_eq_true, Pi.single_eq_of_ne, ZeroMemClass.coe_zero, Matrix.diagonal_apply_ne, LinearMap.zero_apply]
end Rectangular

section Dimension
variable {K : Type portUniverse5} [Field K] [Algebra K D] [Module K V] [IsScalarTower K D V]
variable [Module.Free D V] [Module.Finite D V] [Module.Finite K D]
variable {W : Type portUniverse6} {N : Type portUniverse7} [Fintype W] [Fintype N]
end Dimension
end
end OddKaplansky.IdempotentFree

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.CosetMatrix
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {G : Type portUniverse2} [Field K] [Group G] [Fintype G] (T : Subgroup G)
variable [IsMulCommutative T]
local instance cosetRectangularCommGroup : CommGroup T := { (inferInstance : Group T) with mul_comm := mul_comm' }
variable (p : ℕ) [Fact p.Prime] [CharP K p] (hexp : ∀ t : T, t^p=1)
end
end OddKaplansky.CosetMatrix

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.SectorOrbit
noncomputable section
open scoped Classical BigOperators Matrix
open WreathFourier
variable {K : Type portUniverse1} {H : Type portUniverse2} [Field K] [Group H] [Fintype H]
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
variable (hm : (Fintype.card (Fourier.C M) : K) ≠ 0)
end
end OddKaplansky.SectorOrbit

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.SectorStabilizer
noncomputable section
open scoped Classical BigOperators
variable {G : Type portUniverse1} [Group G] (M : ℕ)
def stabilizer (a : G → ZMod M) : Subgroup G where
  carrier := {g | ∀ x, a (g*x)=a x}
  one_mem' x := by simp only [one_mul]
  mul_mem' hg hh x := by rw [mul_assoc,hg,hh]
  inv_mem' {g} hg x := by have h := hg (g⁻¹*x); simpa only [mul_inv_cancel_left] using h.symm
variable (p : ℕ) [sectionInstance55 : NeZero p] [sectionInstance56 : NeZero M]
abbrev Point := Multiplicative (Fin 3 → ZMod p)
abbrev H := RegularWreathProduct (Multiplicative (ZMod M)) (Point p)
instance : Fintype (H M p) := Fintype.ofFinite _
def baseHom : (Point p → Multiplicative (ZMod M)) →* H M p where
  toFun a := ⟨a,1⟩
  map_one' := rfl
  map_mul' a b := by ext x <;> simp only [Pi.mul_apply, toAdd_mul, RegularWreathProduct.mul_left, inv_one, one_mul, toAdd_one, Pi.zero_apply, RegularWreathProduct.mul_right, mul_one]
lemma base_pow
    (M : Nat)
    (p : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) p]
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (a : Point p → Multiplicative (ZMod M)) : a^M=1 := by
  funext x
  apply Multiplicative.toAdd.injective
  simp only [Pi.pow_apply, toAdd_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, Pi.one_apply, toAdd_one]
lemma pow_of_right (g : H M p) (h : g.right=1) : g^M=1 := by
  have hg : g=baseHom M p g.left := by ext <;> simp only [baseHom, MonoidHom.coe_mk, OneHom.coe_mk, h, toAdd_one, Pi.zero_apply]
  rw [hg,← map_pow,base_pow,map_one]
variable (a : H M p → ZMod M) (ha : ∑ g, a g = 1)
def toPoint : stabilizer M a →* Point p := RegularWreathProduct.rightHom.comp (stabilizer M a).subtype
include ha in
lemma toPoint_kernel (g : stabilizer M a) (hg : toPoint M p a g = 1) : g=1 := by
  apply Subtype.ext
  exact CosetCoordinates.eq_one_of_power_and_sum M a ha g g.property (pow_of_right M p g hg)
include ha in
lemma toPoint_injective : Function.Injective (toPoint M p a) := by
  intro x y h
  have hxy : toPoint M p a (x*y⁻¹)=1 := by rw [map_mul,map_inv,h,mul_inv_cancel]
  exact mul_inv_eq_one.mp (toPoint_kernel M p a ha _ hxy)
include ha in
lemma commutative (x y : stabilizer M a) : x*y=y*x := by
  apply toPoint_injective M p a ha
  rw [map_mul,map_mul,mul_comm]
@[instance_reducible]
def commGroup (ha : ∑ g, a g=1) : CommGroup (stabilizer M a) :=
  { (inferInstance : Group (stabilizer M a)) with mul_comm := commutative M p a ha }
include ha in
lemma exponent (x : stabilizer M a) : x^p=1 := by
  apply toPoint_injective M p a ha
  rw [map_pow,map_one]
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_pow, Pi.smul_apply, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, toAdd_one, Pi.zero_apply]
end
end OddKaplansky.SectorStabilizer

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.SourceSector
noncomputable section
open scoped Classical BigOperators Matrix
open WreathFourier SectorOrbit
variable {K : Type} [Field K] (M p : ℕ) [NeZero M] [Fact p.Prime] [CharP K p]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ M)
end
end OddKaplansky.SourceSector

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.GreedyColumns
noncomputable section
open scoped Classical BigOperators
open Submodule
variable {K : Type portUniverse1} {S : Type portUniverse2} {V : Type portUniverse3} [Field K] [Fintype S] [LinearOrder S]
variable [AddCommGroup V] [Module K V]
variable (v : S → V)

def Selected : Set S := {i | v i ∉ span K (v '' Set.Iio i)}
abbrev Index := {i // Selected (K := K) v i}
instance : Fintype (Index (K := K) v) :=
  @Fintype.ofFinite _ (@Subtype.finite S (Finite.of_fintype S) (Selected (K := K) v))
lemma independent : LinearIndependent K (fun i : Index (K := K) v => v i.val) := by
  classical
  have aux (s : Finset S) : (↑s : Set S) ⊆ Selected (K := K) v → LinearIndepOn K v (↑s : Set S) := by
    induction s using Finset.induction_on_max with
    | empty => intro _; simpa only [Finset.coe_empty] using linearIndepOn_empty K v
    | insert a s hlt ih =>
      intro hs
      rw [Finset.coe_insert]
      apply (ih (fun x hx => hs (by simp only [Finset.coe_insert, Set.mem_insert_iff, hx, or_true]))).insert
      intro ha
      apply hs (show a ∈ (↑(insert a s) : Set S) by simp only [Finset.coe_insert, Set.mem_insert_iff, SetLike.mem_coe, true_or])
      exact span_mono (Set.image_mono (fun x hx => hlt x hx)) ha
  have h := aux (Finset.univ.filter (fun i => i ∈ Selected (K := K) v)) (by simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.ofPred_mem_eq, Std.le_refl])
  change LinearIndepOn K v (Selected (K := K) v)
  convert h using 1
  ext i
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.ofPred_mem_eq]
lemma span_selected : span K (Set.range (fun i : Index (K := K) v => v i.val)) = span K (Set.range v) := by
  classical
  apply le_antisymm
  · apply span_mono
    rintro x ⟨i,rfl⟩
    exact ⟨i.val,rfl⟩
  · apply span_le.mpr
    rintro x ⟨i,rfl⟩
    refine @WellFounded.induction S (· < ·) wellFounded_lt (fun i => v i ∈ span K (Set.range (fun i : Index (K := K) v => v i.val))) i ?_
    intro i ih
    by_cases hi : Selected (K := K) v i
    · exact subset_span ⟨⟨i,hi⟩,rfl⟩
    · have hm : v i ∈ span K (v '' Set.Iio i) := by
        change ¬ (v i ∉ span K (v '' Set.Iio i)) at hi
        exact not_not.mp hi
      apply (span_le.mpr ?_ : span K (v '' Set.Iio i) ≤ span K (Set.range (fun i : Index (K := K) v => v i.val))) hm
      rintro x ⟨j,hj,rfl⟩
      exact ih j (by exact hj)
end
end OddKaplansky.GreedyColumns

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.GreedyLift
noncomputable section
open scoped Classical BigOperators Matrix
open Submodule
variable {K : Type portUniverse1} {S : Type portUniverse2} [Field K] [Fintype S] [LinearOrder S]
variable (E : Matrix S S K) (hE : E*E=E)
abbrev I := GreedyColumns.Index (K := K) E.col
abbrev J := GreedyColumns.Index (K := K) (1-E).col
def columns : I E ⊕ J E → (S → K) := Sum.elim (fun i => E.col i.val) (fun j => (1-E).col j.val)
include hE in
lemma complement : IsCompl (span K (Set.range E.col)) (span K (Set.range (1-E).col)) := by
  let L := Matrix.toLinAlgEquiv' (R := K) (n := S)
  have hi : IsIdempotentElem (L E) := by change L E*L E=L E; rw [← map_mul,hE]
  have hc := LinearMap.IsIdempotentElem.isCompl hi
  rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub hi] at hc
  have hm : L (1-E)=1-L E := by rw [map_sub,map_one]
  rw [← hm] at hc
  change IsCompl (LinearMap.range (Matrix.toLin' E)) (LinearMap.range (Matrix.toLin' (1-E))) at hc
  simpa only [Matrix.range_toLin'] using hc
include hE in
lemma independent : LinearIndependent K (columns E) := by
  apply (GreedyColumns.independent E.col).sum_type (GreedyColumns.independent (1-E).col)
  rw [GreedyColumns.span_selected,GreedyColumns.span_selected]
  exact (complement E hE).disjoint
include hE in
lemma spanning : span K (Set.range (columns E))=⊤ := by
  rw [columns,Set.Sum.elim_range,span_union,GreedyColumns.span_selected,GreedyColumns.span_selected]
  exact (complement E hE).sup_eq_top

def basis : Module.Basis (I E ⊕ J E) K (S → K) :=
  Module.Basis.mk (independent E hE) (spanning E hE).ge
include hE in
lemma card_indices : Fintype.card (I E) + Fintype.card (J E)=Fintype.card S := by
  have hh := Module.finrank_eq_card_basis (basis E hE)
  simpa only [Fintype.card_sum, Module.finrank_fintype_fun_eq_card] using hh.symm

def indices : S ≃ I E ⊕ J E :=
  (FiniteChoice.orderedIndex S).trans ((finCongr (card_indices E hE).symm).trans
    (finSumFinEquiv.symm.trans ((FiniteChoice.orderedIndex (I E)).symm.sumCongr (FiniteChoice.orderedIndex (J E)).symm)))
def matrix : Matrix S S K := fun s t => columns E (indices E hE t) s
lemma matrix_independent : LinearIndependent K (matrix E hE).col :=
  (independent E hE).comp (indices E hE) (indices E hE).injective
lemma matrix_det : (matrix E hE).det ≠ 0 :=
  Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.linearIndependent_col_iff.mp (matrix_independent E hE))
end
end OddKaplansky.GreedyLift

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.GreedyRing
noncomputable section
open scoped Classical BigOperators Matrix
open Submodule
variable {K : Type portUniverse1} {D : Type portUniverse2} {S : Type portUniverse3} [Field K] [CommRing D] [Fintype S] [sectionInstance57 : LinearOrder S]
variable (ε : D →+* K) (unitLift : ∀ d : D, ε d ≠ 0 → IsUnit d)
variable (E : Matrix S S D) (hE : E*E=E)
def E₀ : Matrix S S K := E.map ε
lemma E₀_idem
    {K : Type contextUniverse1}
    {D : Type contextUniverse2}
    {S : Type contextUniverse3}
    [contextInstance3 : Field.{contextUniverse1} K]
    [contextInstance4 : CommRing.{contextUniverse2} D]
    [contextInstance5 : Fintype.{contextUniverse3} S]
    [LinearOrder.{contextUniverse3} S]
    (ε : @RingHom.{contextUniverse2, contextUniverse1} D K
  (@Semiring.toNonAssocSemiring.{contextUniverse2} D
    (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4)))
  (@Semiring.toNonAssocSemiring.{contextUniverse1} K
    (@CommSemiring.toSemiring.{contextUniverse1} K
      (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3)))))
    (E : Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D)
    (hE : @Eq.{max (contextUniverse2 + 1) (contextUniverse3 + 1)} (Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D)
  (@HMul.hMul.{max contextUniverse2 contextUniverse3, max contextUniverse2 contextUniverse3, max contextUniverse2 contextUniverse3} (Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D) (Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D)
    (Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D)
    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{contextUniverse2, contextUniverse3, contextUniverse3, contextUniverse3} S S S D contextInstance5
      (@Distrib.toMul.{contextUniverse2} D
        (@instDistribOfSemiring.{contextUniverse2} D
          (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4))))
      (@Semiring.toAddCommMonoid.{contextUniverse2} D
        (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4))))
    E E)
  E) : E₀ ε E*E₀ ε E=E₀ ε E := by
  change E.map ε*E.map ε=E.map ε
  rw [← Matrix.map_mul,hE]
abbrev I := GreedyLift.I (E₀ ε E)
abbrev J := GreedyLift.J (E₀ ε E)
def columns : I ε E ⊕ J ε E → (S → D) := Sum.elim (fun i => E.col i.val) (fun j => (1-E).col j.val)
def indices : S ≃ I ε E ⊕ J ε E := GreedyLift.indices (E₀ ε E) (E₀_idem ε E hE)

def Q : Matrix S S D := fun s t => columns ε E (indices ε E hE t) s
lemma Q_map : (Q ε E hE).map ε=GreedyLift.matrix (E₀ ε E) (E₀_idem ε E hE) := by
  funext s t
  change ε (columns ε E (indices ε E hE t) s) = GreedyLift.columns (E₀ ε E) (indices ε E hE t) s
  cases hi : indices ε E hE t with
  | inl i => rfl
  | inr j =>
    change ε ((1-E) s j.val)=(1-E₀ ε E) s j.val
    simp only [Matrix.sub_apply,map_sub,E₀,Matrix.map_apply,Matrix.one_apply]
    by_cases h : s=j.val <;> simp only [h, ↓reduceIte, map_one, map_zero, zero_sub]
include unitLift in
lemma Q_det_unit : IsUnit (Q ε E hE).det := by
  apply unitLift
  rw [RingHom.map_det]
  change ((Q ε E hE).map ε).det ≠ 0
  rw [Q_map]
  exact GreedyLift.matrix_det _ _
def equiv : (S → D) ≃ₗ[D] (S → D) :=
  Matrix.toLin'OfInv (Matrix.nonsing_inv_mul (Q ε E hE) (Q_det_unit ε unitLift E hE))
    (Matrix.mul_nonsing_inv (Q ε E hE) (Q_det_unit ε unitLift E hE))
lemma equiv_apply (x : S → D) : equiv ε unitLift E hE x=(Q ε E hE).mulVec x := rfl

def basis : Module.Basis (I ε E ⊕ J ε E) D (S → D) :=
  ((Pi.basisFun D S).map (equiv ε unitLift E hE)).reindex (indices ε E hE)
lemma basis_apply (i : I ε E ⊕ J ε E) : basis ε unitLift E hE i=columns ε E i := by
  rw [basis,Module.Basis.reindex_apply,Module.Basis.map_apply,Pi.basisFun_apply,equiv_apply,Matrix.mulVec_single_one]
  funext s
  change columns ε E (indices ε E hE ((indices ε E hE).symm i)) s=columns ε E i s
  rw [Equiv.apply_symm_apply]
lemma basis_inl (i : I ε E) : basis ε unitLift E hE (Sum.inl i)=E.col i.val := basis_apply ε unitLift E hE _
lemma basis_inr (j : J ε E) : basis ε unitLift E hE (Sum.inr j)=(1-E).col j.val := basis_apply ε unitLift E hE _
lemma fixed_inl (i : I ε E) : Matrix.toLin' E (basis ε unitLift E hE (Sum.inl i))=basis ε unitLift E hE (Sum.inl i) := by
  rw [basis_inl]
  change (E*E).col i.val=E.col i.val
  rw [hE]
lemma killed_inr (j : J ε E) : Matrix.toLin' E (basis ε unitLift E hE (Sum.inr j))=0 := by
  rw [basis_inr]
  change (E*(1-E)).col j.val=0
  rw [mul_sub,mul_one,hE,sub_self]
  rfl
lemma image_independent : LinearIndependent D (fun i : I ε E => basis ε unitLift E hE (Sum.inl i)) :=
  (basis ε unitLift E hE).linearIndependent.comp Sum.inl Sum.inl_injective
lemma image_span : span D (Set.range (fun i : I ε E => basis ε unitLift E hE (Sum.inl i)))=LinearMap.range (Matrix.toLin' E) := by
  apply le_antisymm
  · apply span_le.mpr
    rintro x ⟨i,rfl⟩
    exact ⟨basis ε unitLift E hE (Sum.inl i),fixed_inl ε unitLift E hE i⟩
  · rintro x ⟨y,rfl⟩
    have hy := congrArg (fun z : S → D => Matrix.toLin' E z) ((basis ε unitLift E hE).sum_repr y)
    rw [← hy,map_sum,Fintype.sum_sum_type]
    simp only [map_smul,fixed_inl,killed_inr,smul_zero,Finset.sum_const_zero,add_zero]
    apply Submodule.sum_mem
    intro i _
    exact smul_mem _ _ (subset_span ⟨i,rfl⟩)
def imageBasis : Module.Basis (I ε E) D (LinearMap.range (Matrix.toLin' E)) :=
  (Module.Basis.span (image_independent ε unitLift E hE)).map (LinearEquiv.ofEq _ _ (image_span ε unitLift E hE))
end
end OddKaplansky.GreedyRing

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.GreedyRing
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {T : Type portUniverse2} {S : Type portUniverse3} [Field K] [CommGroup T] [Fintype T] [Fintype S] [LinearOrder S]
variable (p : ℕ) [Fact p.Prime] [CharP K p] (hT : ∀ t : T, t^p=1)
variable (j : T →* Multiplicative (Fin 3 → ZMod p)) (hj : Function.Injective j)
variable (E : Matrix S S (MonoidAlgebra K T)) (hE : E*E=E)
end
end OddKaplansky.GreedyRing

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.GreedyRing
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {D : Type portUniverse2} {S : Type portUniverse3} [Field K] [CommRing D] [Fintype S] [LinearOrder S]
variable (ε : D →+* K) (unitLift : ∀ d : D, ε d ≠ 0 → IsUnit d)
variable (E : Matrix S S D) (hE : E*E=E)
variable {W : Type portUniverse4} {N : Type portUniverse5} [Fintype W] [sectionInstance58 : LinearOrder W] [Fintype N] [sectionInstance59 : LinearOrder N]
variable (hpair : Fintype.card N*Fintype.card S=Fintype.card W*Fintype.card (I ε E))

def pairing : (N×S) ≃ (W×I ε E) :=
  (@FiniteChoice.orderedIndex (N×S) (FiniteChoice.tupleOrder N S) inferInstance).trans
    ((finCongr (by simpa only [Fintype.card_prod] using hpair)).trans
      (@FiniteChoice.orderedIndex (W×I ε E) (FiniteChoice.tupleOrder W (I ε E)) inferInstance).symm)

def coordinateEquiv : (N → S → D) ≃ₗ[D] (W → LinearMap.range (Matrix.toLin' E)) :=
  (LinearEquiv.curry D D N S).symm.trans
    ((LinearEquiv.funCongrLeft D D (pairing ε E hpair).symm).trans
      ((LinearEquiv.curry D D W (I ε E)).trans
        (LinearEquiv.piCongrRight (fun _ : W => (imageBasis ε unitLift E hE).equivFun.symm))))
def rectangleJ : Matrix W N (Module.End D (S → D)) :=
  IdempotentFree.J (Matrix.toLin' E) (coordinateEquiv ε unitLift E hE hpair)
def rectangleY : Matrix N W (Module.End D (S → D)) :=
  IdempotentFree.Y (Matrix.toLin' E) (coordinateEquiv ε unitLift E hE hpair)
lemma rectangleYJ : rectangleY ε unitLift E hE hpair*rectangleJ ε unitLift E hE hpair=1 := by
  have hi : Matrix.toLin' E ∘ₗ Matrix.toLin' E=Matrix.toLin' E := by rw [← Matrix.toLin'_mul,hE]
  convert IdempotentFree.YJ (Matrix.toLin' E) hi (coordinateEquiv ε unitLift E hE hpair) using 1 <;> congr ; exact Subsingleton.elim _ _
lemma rectangleJY : rectangleJ ε unitLift E hE hpair*rectangleY ε unitLift E hE hpair=Matrix.diagonal (fun _ : W => Matrix.toLin' E) := by
  convert IdempotentFree.JY (Matrix.toLin' E) (coordinateEquiv ε unitLift E hE hpair) using 1 <;> congr ; exact Subsingleton.elim _ _
variable [Algebra K D] [Module.Finite K D]
include unitLift hE in
lemma image_dimension : Module.finrank K (LinearMap.range (Matrix.toLin' E))=Fintype.card (I ε E)*Module.finrank K D := by
  have hh := ((imageBasis ε unitLift E hE).equivFun.restrictScalars K).finrank_eq
  simpa only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] using hh
lemma pair_dimension
    {K : Type contextUniverse1}
    {D : Type contextUniverse2}
    {S : Type contextUniverse3}
    [contextInstance3 : Field.{contextUniverse1} K]
    [contextInstance4 : CommRing.{contextUniverse2} D]
    [contextInstance5 : Fintype.{contextUniverse3} S]
    [LinearOrder.{contextUniverse3} S]
    (ε : @RingHom.{contextUniverse2, contextUniverse1} D K
  (@Semiring.toNonAssocSemiring.{contextUniverse2} D
    (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4)))
  (@Semiring.toNonAssocSemiring.{contextUniverse1} K
    (@CommSemiring.toSemiring.{contextUniverse1} K
      (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3)))))
    (unitLift : ∀ (d : D),
  @Ne.{contextUniverse1 + 1} K
      (@DFunLike.coe.{max (contextUniverse1 + 1) (contextUniverse2 + 1), contextUniverse2 + 1, contextUniverse1 + 1}
        (@RingHom.{contextUniverse2, contextUniverse1} D K
          (@Semiring.toNonAssocSemiring.{contextUniverse2} D
            (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4)))
          (@Semiring.toNonAssocSemiring.{contextUniverse1} K
            (@CommSemiring.toSemiring.{contextUniverse1} K
              (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3)))))
        D (fun _ => K)
        (@RingHom.instFunLike.{contextUniverse2, contextUniverse1} D K
          (@Semiring.toNonAssocSemiring.{contextUniverse2} D
            (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4)))
          (@Semiring.toNonAssocSemiring.{contextUniverse1} K
            (@CommSemiring.toSemiring.{contextUniverse1} K
              (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3)))))
        ε d)
      (@OfNat.ofNat.{contextUniverse1} K (nat_lit 0)
        (@Zero.toOfNat0.{contextUniverse1} K
          (@MulZeroClass.toZero.{contextUniverse1} K
            (@instMulZeroClassOfSemiring.{contextUniverse1} K
              (@CommSemiring.toSemiring.{contextUniverse1} K
                (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3))))))) →
    @IsUnit.{contextUniverse2} D
      (@Semiring.toMonoid.{contextUniverse2} D
        (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4)))
      d)
    (E : Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D)
    (hE : @Eq.{max (contextUniverse2 + 1) (contextUniverse3 + 1)} (Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D)
  (@HMul.hMul.{max contextUniverse2 contextUniverse3, max contextUniverse2 contextUniverse3, max contextUniverse2 contextUniverse3} (Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D) (Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D)
    (Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D)
    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{contextUniverse2, contextUniverse3, contextUniverse3, contextUniverse3} S S S D contextInstance5
      (@Distrib.toMul.{contextUniverse2} D
        (@instDistribOfSemiring.{contextUniverse2} D
          (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4))))
      (@Semiring.toAddCommMonoid.{contextUniverse2} D
        (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4))))
    E E)
  E)
    {W : Type contextUniverse4}
    {N : Type contextUniverse5}
    [Fintype.{contextUniverse4} W]
    [LinearOrder.{contextUniverse4} W]
    [Fintype.{contextUniverse5} N]
    [LinearOrder.{contextUniverse5} N]
    [contextInstance17 : @Algebra.{contextUniverse1, contextUniverse2} K D (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3))
  (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4))]
    [@Module.Finite.{contextUniverse1, contextUniverse2} K D
  (@CommSemiring.toSemiring.{contextUniverse1} K (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3)))
  (@Semiring.toAddCommMonoid.{contextUniverse2} D
    (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4)))
  (@Algebra.toModule.{contextUniverse1, contextUniverse2} K D (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3))
    (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4)) contextInstance17)] (hw : Fintype.card W=Module.finrank K (S → D))
    (hn : Fintype.card N=Module.finrank K (LinearMap.range (Matrix.toLin' E))) :
    Fintype.card N*Fintype.card S=Fintype.card W*Fintype.card (I ε E) := by
  rw [hn,hw,image_dimension ε unitLift E hE]
  simp only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
  ring
end
end OddKaplansky.GreedyRing

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.GreedyRing
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {D : Type portUniverse2} {S : Type portUniverse3} [Field K] [CommRing D] [Fintype S] [LinearOrder S]
variable (ε : D →+* K) (unitLift : ∀ d : D, ε d ≠ 0 → IsUnit d)
variable (E : Matrix S S D) (hE : E*E=E)
variable {W : Type portUniverse4} {N : Type portUniverse5} [Fintype W] [LinearOrder W] [Fintype N] [LinearOrder N]
variable (hpair : Fintype.card N*Fintype.card S=Fintype.card W*Fintype.card (I ε E))
end
end OddKaplansky.GreedyRing

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.SourceOrders
noncomputable section
open scoped Classical
variable {H : Type portUniverse1} [Group H] [Fintype H] [LinearOrder H]
@[instance_reducible]
def wreathOrder (M : ℕ) [NeZero M] : LinearOrder (WreathFourier.Wreath (H := H) M) := by
  letI : LinearOrder (Fourier.C M) := cyclic M
  letI : LinearOrder (WreathFourier.Base (H := H) M) := FiniteChoice.functionOrder H (Fourier.C M)
  exact LinearOrder.lift' (fun g : WreathFourier.Wreath (H := H) M => toLex (g.left,g.right)) (by
    intro a b h
    have h' : (a.left,a.right)=(b.left,b.right) := h
    exact RegularWreathProduct.ext (congrArg Prod.fst h') (congrArg Prod.snd h'))
instance localGroupOrder (p M : ℕ) [NeZero p] [NeZero M] : LinearOrder (RegularWreathProduct (Fourier.C M) (Multiplicative (Fin 3 → ZMod p))) :=
  by
    letI : LinearOrder (Multiplicative (Fin 3 → ZMod p)) := point p
    exact wreathOrder M
end
end OddKaplansky.SourceOrders

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.OrderedCosetCoordinates
noncomputable section
open scoped Classical BigOperators
variable {G : Type portUniverse1} [Group G] [Fintype G] [LinearOrder G] (S : Subgroup G)
local instance orderedCoordinatesDecidableEq : DecidableEq G := Classical.decEq G
def rep (q : G ⧸ S) : G := FiniteChoice.first (fun g : G => (g : G ⧸ S)=q) ⟨q.out,Quotient.out_eq' q⟩
lemma rep_mk (q : G ⧸ S) : ((rep S q : G) : G ⧸ S) = q := by
  unfold rep
  exact FiniteChoice.first_spec (fun g : G => (g : G ⧸ S)=q) ⟨q.out,Quotient.out_eq' q⟩
lemma rep_injective : Function.Injective (rep S) := by
  intro q r h
  simpa only [rep_mk] using congrArg (fun g : G => (g : G ⧸ S)) h
@[instance_reducible]
def quotientOrder : LinearOrder (G ⧸ S) := LinearOrder.lift' (rep S) (rep_injective S)
lemma residue_mem (g : G) : (rep S (g : G ⧸ S))⁻¹*g ∈ S :=
  QuotientGroup.eq.mp (rep_mk S (g : G ⧸ S))
def residue (g : G) : S := ⟨_,residue_mem S g⟩
lemma reconstruct (g : G) : rep S (g : G ⧸ S) * residue S g = g := by simp only [residue, mul_inv_cancel_left]
lemma mk_rep_mul (q : G ⧸ S) (s : S) : ((rep S q * (s : G) : G) : G ⧸ S) = q := by
  rw [QuotientGroup.mk_mul_of_mem _ s.property,rep_mk]
lemma residue_rep_mul (q : G ⧸ S) (s : S) : residue S (rep S q * s) = s := by
  apply Subtype.ext
  simp only [residue,mk_rep_mul]
  exact inv_mul_cancel_left _ _
def equiv : G ≃ (G ⧸ S) × S where
  toFun g := ((g : G ⧸ S),residue S g)
  invFun z := rep S z.1 * z.2
  left_inv := reconstruct S
  right_inv z := by ext <;> simp only [mk_rep_mul,residue_rep_mul]
end
end OddKaplansky.OrderedCosetCoordinates

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.OrderedCosetMatrix
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {G : Type portUniverse2} [Field K] [Group G] [sectionInstance60 : Fintype G] [sectionInstance61 : LinearOrder G] (T : Subgroup G)
local instance orderedMatrixDecidableEq : DecidableEq G := Classical.decEq G
abbrev D := MonoidAlgebra K T
open OrderedCosetCoordinates
lemma mk_left
    {G : Type contextUniverse1}
    [contextInstance1 : Group.{contextUniverse1} G]
    [Fintype.{contextUniverse1} G]
    [LinearOrder.{contextUniverse1} G]
    (T : @Subgroup.{contextUniverse1} G contextInstance1) (g h : G) : ((g*h : G) : G ⧸ T) = g • (h : G ⧸ T) := rfl
lemma mk_mul_rep (g : G) (q : G ⧸ T) : ((g*rep T q : G) : G ⧸ T) = g • q := by rw [mk_left,rep_mk]
def cocycle (g : G) (q : G ⧸ T) : T := residue T (g * rep T q)
lemma cocycle_reconstruct (g : G) (q : G ⧸ T) : rep T (g • q) * (cocycle T g q : G) = g*rep T q := by
  simpa only [cocycle,mk_mul_rep] using reconstruct T (g*rep T q)
lemma cocycle_one (q : G ⧸ T) : cocycle T 1 q = 1 := by
  apply Subtype.ext
  simp only [cocycle, residue, one_mul, rep_mk, inv_mul_cancel, OneMemClass.coe_one]
lemma cocycle_mul (g h : G) (q : G ⧸ T) : cocycle T (g*h) q = cocycle T g (h • q) * cocycle T h q := by
  apply Subtype.ext
  apply mul_left_cancel (a := rep T ((g*h) • q))
  rw [cocycle_reconstruct,Subgroup.coe_mul,mul_smul,← mul_assoc,cocycle_reconstruct]
  simp only [mul_assoc,cocycle_reconstruct]

def groupMatrix (g : G) : Matrix (G ⧸ T) (G ⧸ T) (D (K := K) T) := fun q r =>
  if q = g • r then MonoidAlgebra.single (cocycle T g r) 1 else 0
lemma groupMatrix_one : groupMatrix (K := K) T 1 = 1 := by
  funext q r
  simp only [groupMatrix, one_smul, cocycle_one, Matrix.one_apply, MonoidAlgebra.one_def]
lemma groupMatrix_mul (g h : G) : groupMatrix (K := K) T (g*h) = groupMatrix T g * groupMatrix T h := by
  ext q r
  rw [Matrix.mul_apply,Finset.sum_eq_single (h • r)]
  · simp only [groupMatrix,ite_true,ite_mul,zero_mul,      MonoidAlgebra.single_mul_single,one_mul,cocycle_mul,mul_smul]
  · intro z _ hz
    simp only [groupMatrix, hz, ↓reduceIte, mul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]
def representation : MonoidAlgebra K G →ₐ[K] Matrix (G ⧸ T) (G ⧸ T) (D (K := K) T) :=
  MonoidAlgebra.lift K _ G { toFun := groupMatrix T, map_one' := groupMatrix_one T, map_mul' := groupMatrix_mul T }
lemma representation_single (g : G) (c : K) : representation T (MonoidAlgebra.single g c) = c • groupMatrix T g := by
  simp only [representation, MonoidAlgebra.lift_single, MonoidHom.coe_mk, OneHom.coe_mk]

def coefficients {X : Type portUniverse3} [Finite X] : MonoidAlgebra K X ≃ₗ[K] (X → K) :=
  (MonoidAlgebra.coeffLinearEquiv K).trans (Finsupp.linearEquivFunOnFinite K K X)
def unpack : ((G ⧸ T) → D (K := K) T) ≃ₗ[K] MonoidAlgebra K G :=
  (LinearEquiv.piCongrRight (fun _ : G ⧸ T => coefficients)).trans
    ((LinearEquiv.curry K K (G ⧸ T) T).symm.trans
      ((LinearEquiv.piCongrLeft K (fun _ : (G ⧸ T) × T => K) (equiv T)).symm.trans coefficients.symm))
lemma unpack_coeff (v : (G ⧸ T) → D (K := K) T) (g : G) :
    (unpack T v).coeff g = (v (g : G ⧸ T)).coeff (residue T g) := rfl
lemma residue_left (g x : G) : residue T (g*x) = cocycle T g (x : G ⧸ T) * residue T x := by
  apply Subtype.ext
  apply mul_left_cancel (a := rep T ((g*x : G) : G ⧸ T))
  rw [reconstruct,Subgroup.coe_mul,mk_left,← mul_assoc,cocycle_reconstruct,mul_assoc,reconstruct]
lemma groupMatrix_mulVec (g : G) (v : (G ⧸ T) → D (K := K) T) (q : G ⧸ T) :
    (groupMatrix T g).mulVec v q = MonoidAlgebra.single (cocycle T g (g⁻¹ • q)) 1 * v (g⁻¹ • q) := by
  rw [Matrix.mulVec, dotProduct,Finset.sum_eq_single (g⁻¹ • q)]
  · simp only [groupMatrix, smul_inv_smul, ↓reduceIte]
  · intro r _ hr
    have hne : q ≠ g • r := by
      intro he
      apply hr
      rw [he,inv_smul_smul]
    simp only [groupMatrix, hne, ↓reduceIte, zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]
lemma unpack_group (g : G) (v : (G ⧸ T) → D (K := K) T) :
    unpack T ((groupMatrix T g).mulVec v) = MonoidAlgebra.single g 1 * unpack T v := by
  apply MonoidAlgebra.coeff_injective
  ext x
  rw [unpack_coeff,groupMatrix_mulVec,MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_single_mul_apply,unpack_coeff,one_mul,one_mul]
  have hq : ((g⁻¹*x : G) : G ⧸ T) = g⁻¹ • (x : G ⧸ T) := rfl
  have hr := residue_left T g (g⁻¹*x)
  simp only [mul_inv_cancel_left,hq] at hr
  rw [hq,hr,inv_mul_cancel_left]
lemma unpack_representation (e : MonoidAlgebra K G) (v : (G ⧸ T) → D (K := K) T) :
    unpack T ((representation T e).mulVec v) = e * unpack T v := by
  induction e using MonoidAlgebra.induction_on with
  | of g => simpa only [MonoidAlgebra.of_apply,representation_single,one_smul] using unpack_group T g v
  | add e f he hf => simp only [map_add,Matrix.add_mulVec,he,hf,add_mul]
  | smul c e he => simp only [map_smul,Matrix.smul_mulVec,map_smul,he,smul_mul_assoc]

section Commutative
variable [IsMulCommutative T]
local instance orderedMatrixCommGroup : CommGroup T := { (inferInstance : Group T) with mul_comm := mul_comm' }
def endomorphism (e : MonoidAlgebra K G) : Module.End (D (K := K) T) ((G ⧸ T) → D (K := K) T) :=
  Matrix.toLin' (representation T e)
lemma endomorphism_rank (e : MonoidAlgebra K G) :
    Module.finrank K (LinearMap.range (endomorphism T e)) =
      Module.finrank K (LinearMap.range (Algebra.lmul K (MonoidAlgebra K G) e)) := by
  have ht : (unpack (K := K) T).toLinearMap.comp ((endomorphism T e).restrictScalars K) =
      (Algebra.lmul K (MonoidAlgebra K G) e).comp (unpack T).toLinearMap := by
    apply LinearMap.ext
    intro v
    exact unpack_representation T e v
  have hr := congrArg LinearMap.range ht
  rw [LinearMap.range_comp,LinearMap.range_comp,LinearEquiv.range,Submodule.map_top] at hr
  have hd := LinearEquiv.finrank_map_eq (unpack (K := K) T) (LinearMap.range ((endomorphism T e).restrictScalars K))
  rw [hr] at hd
  rw [LinearMap.range_restrictScalars] at hd
  have hx := ((Submodule.restrictScalarsEquiv K (D (K := K) T) _ (LinearMap.range (endomorphism T e))).restrictScalars K).finrank_eq
  exact hx.symm.trans hd.symm
end Commutative
end
end OddKaplansky.OrderedCosetMatrix

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.OrderedOrbitBlock
noncomputable section
open scoped Classical BigOperators Matrix
open WreathFourier OrderedCosetCoordinates
variable {K : Type portUniverse1} {H : Type portUniverse2} [Field K] [Group H] [Fintype H] [sectionInstance62 : LinearOrder H]
local instance orderedOrbitBlockDecidableEq : DecidableEq H := Classical.decEq H
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
variable (lmb : Base (H := H) M) (T : Subgroup H)
variable (hT : ∀ g : H, g ∈ T ↔ shift M g lmb = lmb)
lemma shift_eq_iff
    {H : Type contextUniverse1}
    [contextInstance1 : Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    [LinearOrder.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    (lmb : @OddKaplansky.WreathFourier.Base.{contextUniverse1} H M)
    (T : @Subgroup.{contextUniverse1} H contextInstance1)
    (hT : ∀ (g : H),
  Iff
    (@Membership.mem.{contextUniverse1, contextUniverse1} H (@Subgroup.{contextUniverse1} H contextInstance1)
      (@SetLike.instMembership.{contextUniverse1, contextUniverse1} (@Subgroup.{contextUniverse1} H contextInstance1) H
        (@Subgroup.instSetLike.{contextUniverse1} H contextInstance1))
      T g)
    (@Eq.{contextUniverse1 + 1} (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M)
      (@DFunLike.coe.{contextUniverse1 + 1, contextUniverse1 + 1, contextUniverse1 + 1}
        (@MulEquiv.{contextUniverse1, contextUniverse1} (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M) (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M)
          (@Pi.instMul.{contextUniverse1, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
            @Multiplicative.mul.{0} (ZMod M)
              (@Distrib.toAdd.{0} (ZMod M)
                (@instDistribOfSemiring.{0} (ZMod M)
                  (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))
          (@Pi.instMul.{contextUniverse1, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
            @Multiplicative.mul.{0} (ZMod M)
              (@Distrib.toAdd.{0} (ZMod M)
                (@instDistribOfSemiring.{0} (ZMod M)
                  (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M)))))))
        (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M) (fun _ => @OddKaplansky.WreathFourier.Base.{contextUniverse1} H M)
        (@EquivLike.toFunLike.{contextUniverse1 + 1, contextUniverse1 + 1, contextUniverse1 + 1}
          (@MulEquiv.{contextUniverse1, contextUniverse1} (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M)
            (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M)
            (@Pi.instMul.{contextUniverse1, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
              @Multiplicative.mul.{0} (ZMod M)
                (@Distrib.toAdd.{0} (ZMod M)
                  (@instDistribOfSemiring.{0} (ZMod M)
                    (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))
            (@Pi.instMul.{contextUniverse1, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
              @Multiplicative.mul.{0} (ZMod M)
                (@Distrib.toAdd.{0} (ZMod M)
                  (@instDistribOfSemiring.{0} (ZMod M)
                    (@CommSemiring.toSemiring.{0} (ZMod M)
                      (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M)))))))
          (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M) (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M)
          (@MulEquiv.instEquivLike.{contextUniverse1, contextUniverse1} (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M)
            (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M)
            (@Pi.instMul.{contextUniverse1, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
              @Multiplicative.mul.{0} (ZMod M)
                (@Distrib.toAdd.{0} (ZMod M)
                  (@instDistribOfSemiring.{0} (ZMod M)
                    (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))
            (@Pi.instMul.{contextUniverse1, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
              @Multiplicative.mul.{0} (ZMod M)
                (@Distrib.toAdd.{0} (ZMod M)
                  (@instDistribOfSemiring.{0} (ZMod M)
                    (@CommSemiring.toSemiring.{0} (ZMod M)
                      (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))))
        (@OddKaplansky.WreathFourier.shift.{contextUniverse1} H contextInstance1 M g) lmb)
      lmb)) (g h : H) : shift M g lmb = shift M h lmb ↔ (g : H ⧸ T) = h := by
  rw [QuotientGroup.eq,hT]
  constructor
  · intro he
    rw [shift_mul,← he,← shift_mul,inv_mul_cancel,shift_one]
    rfl
  · intro he
    have hh := congrArg (shift M g) he
    simpa only [← shift_mul,mul_inv_cancel_left] using hh.symm
def unit (q r : H ⧸ T) (t : T) : MonoidAlgebra K (Wreath (H := H) M) :=
  normal M hζ (shift M (rep T q) lmb) (rep T q * t * (rep T r)⁻¹)
include hT hc in
lemma unit_mul (q r s z : H ⧸ T) (t u : T) :
    unit M hζ lmb T q r t * unit M hζ lmb T s z u =
      if r=s then unit M hζ lmb T q z (t*u) else 0 := by
  rw [unit,unit,normal_mul M hζ hc]
  have he : shift M (rep T q) lmb = shift M (rep T q * t * (rep T r)⁻¹) (shift M (rep T s) lmb) ↔ r=s := by
    rw [← shift_mul,shift_eq_iff M lmb T hT]
    constructor
    · intro hh
      have hm : (rep T q)⁻¹ * (rep T q * t * (rep T r)⁻¹ * rep T s) ∈ T := QuotientGroup.eq.mp hh
      have hr : (rep T r)⁻¹ * rep T s ∈ T := by
        have hmul := T.mul_mem (T.inv_mem t.property) hm
        simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel_left] using hmul
      have hf := QuotientGroup.eq.mpr hr
      simpa only [rep_mk] using hf
    · intro hrs
      subst s
      simp only [mul_assoc,inv_mul_cancel,mul_one,mk_rep_mul,rep_mk]
  by_cases h : r=s
  · rw [if_pos (he.mpr h),if_pos h]
    subst s
    simp only [unit,Subgroup.coe_mul,mul_assoc,inv_mul_cancel_left]
  · rw [if_neg (fun hh => h (he.mp hh)),if_neg h]

def entry (q r : H ⧸ T) : MonoidAlgebra K T →ₗ[K] MonoidAlgebra K (Wreath (H := H) M) where
  toFun a := ∑ t : T, a.coeff t • unit M hζ lmb T q r t
  map_add' a b := by simp only [MonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp only [MonoidAlgebra.coeff_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]
lemma entry_apply (q r : H ⧸ T) (a : MonoidAlgebra K T) :
    entry M hζ lmb T q r a = ∑ t : T, a.coeff t • unit M hζ lmb T q r t := rfl
lemma entry_single (q r : H ⧸ T) (t : T) (c : K) :
    entry M hζ lmb T q r (MonoidAlgebra.single t c) = c • unit M hζ lmb T q r t := by
  rw [entry_apply]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
include hT hc in
lemma entry_mul (q r s z : H ⧸ T) (a b : MonoidAlgebra K T) :
    entry M hζ lmb T q r a * entry M hζ lmb T s z b =
      if r=s then entry M hζ lmb T q z (a*b) else 0 := by
  induction a using MonoidAlgebra.induction_on with
  | of t =>
    induction b using MonoidAlgebra.induction_on with
    | of u => simp only [MonoidAlgebra.of_apply,entry_single,one_smul,MonoidAlgebra.single_mul_single,one_mul,unit_mul M hζ hc lmb T hT]
    | add b c hb hc => simp only [map_add,mul_add,hb,hc]; split_ifs <;> simp only [MonoidAlgebra.of_apply, add_zero]
    | smul c b hb => simp only [map_smul,mul_smul_comm,hb]; split_ifs <;> simp only [MonoidAlgebra.of_apply, smul_zero]
  | add a c ha hc => simp only [map_add,add_mul,ha,hc]; split_ifs <;> simp only [add_zero]
  | smul c a ha => simp only [map_smul,smul_mul_assoc,ha]; split_ifs <;> simp only [smul_zero]

def lift : Matrix (H ⧸ T) (H ⧸ T) (MonoidAlgebra K T) →ₗ[K] MonoidAlgebra K (Wreath (H := H) M) where
  toFun F := ∑ q, ∑ r, entry M hζ lmb T q r (F q r)
  map_add' F G := by simp only [Matrix.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c F := by simp only [Matrix.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]
lemma lift_apply (F : Matrix (H ⧸ T) (H ⧸ T) (MonoidAlgebra K T)) :
    lift M hζ lmb T F = ∑ q, ∑ r, entry M hζ lmb T q r (F q r) := rfl
include hT hc in
lemma entry_lift (q r : H ⧸ T) (a : MonoidAlgebra K T)
    (G : Matrix (H ⧸ T) (H ⧸ T) (MonoidAlgebra K T)) :
    entry M hζ lmb T q r a * lift M hζ lmb T G =
      ∑ z, entry M hζ lmb T q z (a * G r z) := by
  simp only [lift_apply,Finset.mul_sum,entry_mul M hζ hc lmb T hT,Finset.sum_ite_irrel,
    Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
include hT hc in
lemma lift_mul (F G : Matrix (H ⧸ T) (H ⧸ T) (MonoidAlgebra K T)) :
    lift M hζ lmb T F * lift M hζ lmb T G = lift M hζ lmb T (F*G) := by
  rw [lift_apply]
  simp only [Finset.sum_mul,entry_lift M hζ hc lmb T hT]
  rw [lift_apply]
  simp only [Matrix.mul_apply,map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact Finset.sum_comm

def identity : MonoidAlgebra K (Wreath (H := H) M) := ∑ q : H ⧸ T, projector M hζ (shift M (rep T q) lmb)
lemma entry_one (q r : H ⧸ T) : entry M hζ lmb T q r 1 = unit M hζ lmb T q r 1 := by
  rw [MonoidAlgebra.one_def,entry_single,one_smul]
lemma lift_one : lift M hζ lmb T 1 = identity M hζ lmb T := by
  simp only [lift_apply, Matrix.one_apply, apply_ite, entry_one, unit, normal, OneMemClass.coe_one, mul_one, map_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, mul_inv_cancel, topElt_one, identity]
lemma unit_cocycle (g : H) (r : H ⧸ T) :
    unit M hζ lmb T (g • r) r (OrderedCosetMatrix.cocycle T g r) =
      normal M hζ (shift M (rep T (g • r)) lmb) g := by
  rw [unit,OrderedCosetMatrix.cocycle_reconstruct,mul_inv_cancel_right]
lemma lift_groupMatrix (g : H) :
    lift M hζ lmb T (OrderedCosetMatrix.groupMatrix T g) = identity M hζ lmb T * topElt M g := by
  rw [lift_apply,Finset.sum_comm]
  simp only [OrderedCosetMatrix.groupMatrix,apply_ite,map_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    entry_single,one_smul,unit_cocycle]
  rw [identity,Finset.sum_mul]
  exact Equiv.sum_comp (MulAction.toPerm g) (fun q : H ⧸ T => normal M hζ (shift M (rep T q) lmb) g)
lemma lift_representation (e : MonoidAlgebra K H) :
    lift M hζ lmb T (OrderedCosetMatrix.representation T e) =
      identity M hζ lmb T * MonoidAlgebra.mapDomainAlgHom K K (top M) e := by
  induction e using MonoidAlgebra.induction_on with
  | of g => simpa only [MonoidAlgebra.of_apply,OrderedCosetMatrix.representation_single,one_smul,
      MonoidAlgebra.mapDomainAlgHom_apply,MonoidAlgebra.mapDomain_single,topElt] using lift_groupMatrix M hζ lmb T g
  | add a b ha hb => simp only [map_add,mul_add,ha,hb]
  | smul c a ha => simp only [map_smul,mul_smul_comm,ha]
section Cross
variable (mu : Base (H := H) M) (U : Subgroup H)
variable (hsep : ∀ g : H, lmb ≠ shift M g mu)
include hc hsep in
lemma unit_cross (q r : H ⧸ T) (s z : H ⧸ U) (t : T) (u : U) :
    unit M hζ lmb T q r t * unit M hζ mu U s z u = 0 := by
  rw [unit,unit,normal_mul M hζ hc]
  apply if_neg
  intro he
  apply hsep ((rep T q)⁻¹ * (rep T q * t * (rep T r)⁻¹) * rep U s)
  have hh := congrArg (shift M (rep T q)⁻¹) he
  simpa only [← shift_mul,inv_mul_cancel,shift_one,MulEquiv.refl_apply,mul_assoc] using hh
include hc hsep in
lemma entry_cross (q r : H ⧸ T) (s z : H ⧸ U) (a : MonoidAlgebra K T) (b : MonoidAlgebra K U) :
    entry M hζ lmb T q r a * entry M hζ mu U s z b = 0 := by
  rw [entry_apply,entry_apply]
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,
    unit_cross M hζ hc lmb T mu U hsep,smul_zero,Finset.sum_const_zero]
include hc hsep in
lemma lift_cross (F : Matrix (H ⧸ T) (H ⧸ T) (MonoidAlgebra K T))
    (G : Matrix (H ⧸ U) (H ⧸ U) (MonoidAlgebra K U)) :
    lift M hζ lmb T F * lift M hζ mu U G = 0 := by
  rw [lift_apply,lift_apply]
  simp only [Finset.sum_mul,Finset.mul_sum,entry_cross M hζ hc lmb T mu U hsep,Finset.sum_const_zero]
end Cross
end
end OddKaplansky.OrderedOrbitBlock

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.OrderedSectorOrbit
noncomputable section
open scoped Classical BigOperators Matrix
open WreathFourier OrderedCosetCoordinates
variable {K : Type portUniverse1} {H : Type portUniverse2} [Field K] [Group H] [Fintype H] [LinearOrder H]
local instance orderedOrbitDecidableEq : DecidableEq H := Classical.decEq H
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
@[instance_reducible]
def action : MulAction H (Base (H := H) M) where
  smul g a := shift M g a
  one_smul a := by change shift M 1 a=a; rw [shift_one]; rfl
  mul_smul g h a := shift_mul M g h a
local instance : MulAction H (Base (H := H) M) := action M
abbrev Rep := OrbitSelection.Rep (H := H) (fun a : Base (H := H) M => SectorFourier.weight M a=1)
@[instance_reducible]
def characterOrder : LinearOrder (Base (H := H) M) := @FiniteChoice.functionOrder H (Fourier.C M) inferInstance inferInstance (SourceOrders.cyclic M)
def lmb (r : Rep (H := H) M) : Base (H := H) M := OrbitSelection.Ordered.representative (H := H) (characterOrder M) _ r
lemma lmb_spec (r : Rep (H := H) M) :
    (Quotient.mk'' (lmb M r) : MulAction.orbitRel.Quotient H (Base (H := H) M))=r.val ∧ SectorFourier.weight M (lmb M r)=1 :=
  OrbitSelection.Ordered.representative_spec (characterOrder M) _ r
lemma cover (a : Base (H := H) M) (ha : SectorFourier.weight M a=1) : ∃ r : Rep (H := H) M, ∃ h : H, shift M h (lmb M r)=a := by
  let r : Rep (H := H) M := ⟨Quotient.mk'' a,⟨a,rfl,ha⟩⟩
  refine ⟨r,?_⟩
  have hh : (Quotient.mk'' a : MulAction.orbitRel.Quotient H (Base (H := H) M))=Quotient.mk'' (lmb M r) := (lmb_spec M r).1.symm
  exact Quotient.exact hh
lemma lmb_weight (r : Rep (H := H) M) : SectorFourier.weight M (lmb M r)=1 := (lmb_spec M r).2
def T (r : Rep (H := H) M) : Subgroup H := MulAction.stabilizer H (lmb M r)
lemma mem_T (r : Rep (H := H) M) (g : H) : g ∈ T M r ↔ shift M g (lmb M r)=lmb M r := Iff.rfl
lemma separate {r s : Rep (H := H) M} (hrs : r≠s) (g : H) : lmb M r ≠ shift M g (lmb M s) := by
  intro he
  apply hrs
  apply Subtype.ext
  have hh : (Quotient.mk'' (lmb M r) : MulAction.orbitRel.Quotient H (Base (H := H) M)) = Quotient.mk'' (lmb M s) :=
    Quotient.sound ⟨g,he.symm⟩
  exact (lmb_spec M r).1.symm.trans (hh.trans (lmb_spec M s).1)
def orbitMap (z : (r : Rep (H := H) M) × (H ⧸ T M r)) :
    {a : Base (H := H) M // SectorFourier.weight M a=1} :=
  ⟨shift M (rep (T M z.1) z.2) (lmb M z.1), (SectorFourier.weight_shift M _ _).trans (lmb_weight M _)⟩
lemma orbitMap_injective : Function.Injective (orbitMap (H := H) M) := by
  rintro ⟨r,q⟩ ⟨s,t⟩ he
  have hv := congrArg Subtype.val he
  have hrs : r=s := by
    by_contra hn
    apply separate M hn ((rep (T M r) q)⁻¹ * rep (T M s) t)
    have hh := congrArg (shift M (rep (T M r) q)⁻¹) hv
    simpa only [orbitMap,← shift_mul,inv_mul_cancel,shift_one,MulEquiv.refl_apply] using hh
  subst s
  have hqt := (OrderedOrbitBlock.shift_eq_iff M (lmb M r) (T M r) (mem_T M r) _ _).mp hv
  rw [rep_mk,rep_mk] at hqt
  exact Sigma.mk.inj_iff.mpr ⟨rfl,heq_of_eq hqt⟩
lemma orbitMap_surjective : Function.Surjective (orbitMap (H := H) M) := by
  intro a
  obtain ⟨r,g,hg⟩ := cover M a.val a.property
  have hg' : shift M g (lmb M r)=a.val := hg
  refine ⟨⟨r,(g : H ⧸ T M r)⟩,?_⟩
  apply Subtype.ext
  change shift M (rep (T M r) (g : H ⧸ T M r)) (lmb M r)=a.val
  rw [← hg']
  exact (OrderedOrbitBlock.shift_eq_iff M (lmb M r) (T M r) (mem_T M r) _ _).mpr (rep_mk _ _)
def orbitEquiv : ((r : Rep (H := H) M) × (H ⧸ T M r)) ≃
    {a : Base (H := H) M // SectorFourier.weight M a=1} :=
  Equiv.ofBijective (orbitMap M) ⟨orbitMap_injective M,orbitMap_surjective M⟩
lemma identity_sum (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
    (hm : (Fintype.card (Fourier.C M) : K) ≠ 0) :
    ∑ r : Rep (H := H) M, OrderedOrbitBlock.identity M hζ (lmb M r) (T M r) = SectorFourier.f M hζ := by
  apply Eq.trans ?_ (SectorFourier.f_eq_packet (H := H) M hζ hc hm).symm
  have hh := Equiv.sum_comp (orbitEquiv (H := H) M) (fun a => projector M hζ a.val)
  change (∑ z : (r : Rep (H := H) M) × (H ⧸ T M r), projector M hζ (shift M (rep (T M z.1) z.2) (lmb M z.1))) = _ at hh
  simpa only [Fintype.sum_sigma,OrderedOrbitBlock.identity] using hh

variable (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
abbrev Block (r : Rep (H := H) M) := Matrix (H ⧸ T M r) (H ⧸ T M r) (MonoidAlgebra K (T M r))
def pack : ((r : Rep (H := H) M) → Block (K := K) M r) →ₗ[K] MonoidAlgebra K (Wreath (H := H) M) where
  toFun F := ∑ r, OrderedOrbitBlock.lift M hζ (lmb M r) (T M r) (F r)
  map_add' F G := by simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
  map_smul' c F := by simp only [Pi.smul_apply,map_smul,RingHom.id_apply,Finset.smul_sum]
lemma pack_apply (F : (r : Rep (H := H) M) → Block (K := K) M r) :
    pack M hζ F = ∑ r, OrderedOrbitBlock.lift M hζ (lmb M r) (T M r) (F r) := rfl
include hc in
lemma pack_mul (F G : (r : Rep (H := H) M) → Block (K := K) M r) :
    pack M hζ F * pack M hζ G = pack M hζ (fun r => F r*G r) := by
  rw [pack_apply,pack_apply,Finset.sum_mul,pack_apply]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum,Finset.sum_eq_single r]
  · exact OrderedOrbitBlock.lift_mul M hζ hc (lmb M r) (T M r) (mem_T M r) (F r) (G r)
  · intro s _ hsr
    exact OrderedOrbitBlock.lift_cross M hζ hc (lmb M r) (T M r) (lmb M s) (T M s) (separate M hsr.symm) (F r) (G s)
  · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]
include hc in
lemma pack_one (hm : (Fintype.card (Fourier.C M) : K) ≠ 0) :
    pack (H := H) M hζ (fun _ => 1) = SectorFourier.f M hζ := by
  simp only [pack_apply,OrderedOrbitBlock.lift_one]
  exact identity_sum M hζ hc hm
include hc in
lemma pack_representation (e : MonoidAlgebra K H) (hm : (Fintype.card (Fourier.C M) : K) ≠ 0) :
    pack M hζ (fun r => OrderedCosetMatrix.representation (T M r) e) =
      SectorFourier.f M hζ * MonoidAlgebra.mapDomainAlgHom K K (top M) e := by
  simp only [pack_apply,OrderedOrbitBlock.lift_representation,← Finset.sum_mul,identity_sum M hζ hc hm]
end
end OddKaplansky.OrderedSectorOrbit

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.OrderedSectorOrbit
noncomputable section
open scoped Classical BigOperators Matrix
open WreathFourier
variable {K : Type portUniverse1} {H : Type portUniverse2} [Field K] [Group H] [Fintype H] [LinearOrder H]
local instance orderedSectorRectangularDecidableEq : DecidableEq H := Classical.decEq H
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
variable (hm : (Fintype.card (Fourier.C M) : K) ≠ 0)
def matrixPack {W : Type portUniverse3} {N : Type portUniverse4} (F : (r : Rep (H := H) M) → Matrix W N (Block (K := K) M r)) :
    Matrix W N (MonoidAlgebra K (Wreath (H := H) M)) := fun w n => pack M hζ (fun r => F r w n)
include hc in
lemma matrixPack_mul {W : Type portUniverse5} {N : Type portUniverse6} {V : Type portUniverse7} [Fintype N]
    (F : (r : Rep (H := H) M) → Matrix W N (Block (K := K) M r))
    (G : (r : Rep (H := H) M) → Matrix N V (Block (K := K) M r)) :
    matrixPack M hζ F * matrixPack M hζ G = matrixPack M hζ (fun r => F r*G r) := by
  funext w v
  simp only [Matrix.mul_apply,matrixPack,pack_mul M hζ hc]
  rw [← map_sum]
  congr 1
  funext r
  simp only [Finset.sum_apply,]
include hc hm in
lemma matrixPack_one {N : Type portUniverse8} [DecidableEq N] :
    matrixPack (H := H) M hζ (fun _ => (1 : Matrix N N _)) = Matrix.diagonal (fun _ : N => SectorFourier.f M hζ) := by
  funext n n'
  simp only [matrixPack,Matrix.one_apply,Matrix.diagonal_apply]
  by_cases h : n=n'
  · simp only [h,ite_true,pack_one M hζ hc hm]
  · simp only [if_neg h]
    exact map_zero _
include hc hm in
lemma pack_left_sector (F : (r : Rep (H := H) M) → Block (K := K) M r) :
    SectorFourier.f M hζ * pack M hζ F = pack M hζ F := by
  rw [← pack_one M hζ hc hm,pack_mul M hζ hc]
  simp only [one_mul]
end
end OddKaplansky.OrderedSectorOrbit

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.OrderedSourceSector
noncomputable section
open scoped Classical BigOperators Matrix
open WreathFourier OrderedSectorOrbit
lemma T_leftFixed {H : Type portUniverse1} [Group H] [Fintype H] [LinearOrder H] (M : ℕ) [NeZero M] (r : Rep (H := H) M) :
    T M r = SectorStabilizer.stabilizer M (fun x => (lmb M r x).toAdd) := by
  ext g
  rw [mem_T]
  constructor
  · intro he x
    have hh := congrArg (fun a : Base (H := H) M => (a (g*x)).toAdd) he
    simpa only [shift_apply,inv_mul_cancel_left] using hh.symm
  · intro hg
    funext x
    apply Multiplicative.toAdd.injective
    have hh := hg (g⁻¹*x)
    simpa only [shift_apply,mul_inv_cancel_left] using hh.symm
end
end OddKaplansky.OrderedSourceSector

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.OrderedCosetMatrix
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {G : Type portUniverse2} [Field K] [Group G] [sectionInstance63 : Fintype G] [sectionInstance64 : LinearOrder G] (T : Subgroup G)
local instance orderedGreedyGroupDecidableEq : DecidableEq G := Classical.decEq G
variable [sectionInstance65 : IsMulCommutative T]
local instance orderedGreedyCommGroup : CommGroup T := { (inferInstance : Group T) with mul_comm := mul_comm' }
local instance orderedGreedyQuotientOrder : LinearOrder (G ⧸ T) := OrderedCosetCoordinates.quotientOrder T
local instance orderedGreedyQuotientDecidableEq : DecidableEq (G ⧸ T) := Classical.decEq _
variable (p : ℕ) [Fact p.Prime] [CharP K p] (hexp : ∀ t : T, t^p=1)
def augmentation : D (K := K) T →+* K := LocalAlgebra.augment.toRingHom
lemma augmentation_unit
    {K : Type contextUniverse1}
    {G : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [contextInstance3 : Group.{contextUniverse2} G]
    [Fintype.{contextUniverse2} G]
    [LinearOrder.{contextUniverse2} G]
    (T : @Subgroup.{contextUniverse2} G contextInstance3)
    [@IsMulCommutative.{contextUniverse2}
  (@Subtype.{contextUniverse2 + 1} G fun x =>
    @Membership.mem.{contextUniverse2, contextUniverse2} G (@Subgroup.{contextUniverse2} G contextInstance3)
      (@SetLike.instMembership.{contextUniverse2, contextUniverse2} (@Subgroup.{contextUniverse2} G contextInstance3) G
        (@Subgroup.instSetLike.{contextUniverse2} G contextInstance3))
      T x)
  (@Subgroup.mul.{contextUniverse2} G contextInstance3 T)]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p]
    (hexp : ∀
  (t :
    @Subtype.{contextUniverse2 + 1} G fun x =>
      @Membership.mem.{contextUniverse2, contextUniverse2} G (@Subgroup.{contextUniverse2} G contextInstance3)
        (@SetLike.instMembership.{contextUniverse2, contextUniverse2} (@Subgroup.{contextUniverse2} G contextInstance3) G
          (@Subgroup.instSetLike.{contextUniverse2} G contextInstance3))
        T x),
  @Eq.{contextUniverse2 + 1}
    (@Subtype.{contextUniverse2 + 1} G fun x =>
      @Membership.mem.{contextUniverse2, contextUniverse2} G (@Subgroup.{contextUniverse2} G contextInstance3)
        (@SetLike.instMembership.{contextUniverse2, contextUniverse2} (@Subgroup.{contextUniverse2} G contextInstance3) G
          (@Subgroup.instSetLike.{contextUniverse2} G contextInstance3))
        T x)
    (@HPow.hPow.{contextUniverse2, 0, contextUniverse2}
      (@Subtype.{contextUniverse2 + 1} G fun x =>
        @Membership.mem.{contextUniverse2, contextUniverse2} G (@Subgroup.{contextUniverse2} G contextInstance3)
          (@SetLike.instMembership.{contextUniverse2, contextUniverse2} (@Subgroup.{contextUniverse2} G contextInstance3) G
            (@Subgroup.instSetLike.{contextUniverse2} G contextInstance3))
          T x)
      Nat
      (@Subtype.{contextUniverse2 + 1} G fun x =>
        @Membership.mem.{contextUniverse2, contextUniverse2} G (@Subgroup.{contextUniverse2} G contextInstance3)
          (@SetLike.instMembership.{contextUniverse2, contextUniverse2} (@Subgroup.{contextUniverse2} G contextInstance3) G
            (@Subgroup.instSetLike.{contextUniverse2} G contextInstance3))
          T x)
      (@instHPow.{contextUniverse2, 0}
        (@Subtype.{contextUniverse2 + 1} G fun x =>
          @Membership.mem.{contextUniverse2, contextUniverse2} G (@Subgroup.{contextUniverse2} G contextInstance3)
            (@SetLike.instMembership.{contextUniverse2, contextUniverse2} (@Subgroup.{contextUniverse2} G contextInstance3) G
              (@Subgroup.instSetLike.{contextUniverse2} G contextInstance3))
            T x)
        Nat (@Subgroup.npow.{contextUniverse2} G contextInstance3 T))
      t p)
    (@OfNat.ofNat.{contextUniverse2}
      (@Subtype.{contextUniverse2 + 1} G fun x =>
        @Membership.mem.{contextUniverse2, contextUniverse2} G (@Subgroup.{contextUniverse2} G contextInstance3)
          (@SetLike.instMembership.{contextUniverse2, contextUniverse2} (@Subgroup.{contextUniverse2} G contextInstance3) G
            (@Subgroup.instSetLike.{contextUniverse2} G contextInstance3))
          T x)
      (nat_lit 1)
      (@One.toOfNat1.{contextUniverse2}
        (@Subtype.{contextUniverse2 + 1} G fun x =>
          @Membership.mem.{contextUniverse2, contextUniverse2} G (@Subgroup.{contextUniverse2} G contextInstance3)
            (@SetLike.instMembership.{contextUniverse2, contextUniverse2} (@Subgroup.{contextUniverse2} G contextInstance3) G
              (@Subgroup.instSetLike.{contextUniverse2} G contextInstance3))
            T x)
        (@Subgroup.one.{contextUniverse2} G contextInstance3 T)))) (x : D (K := K) T) (hx : augmentation T x≠0) : IsUnit x :=
  (LocalAlgebra.isUnit_iff p hexp x).mpr hx
variable (e : MonoidAlgebra K G) (he : e*e=e)
lemma representation_idempotent
    {K : Type contextUniverse1}
    {G : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [contextInstance3 : Group.{contextUniverse2} G]
    [Fintype.{contextUniverse2} G]
    [LinearOrder.{contextUniverse2} G]
    (T : @Subgroup.{contextUniverse2} G contextInstance3)
    [@IsMulCommutative.{contextUniverse2}
  (@Subtype.{contextUniverse2 + 1} G fun x =>
    @Membership.mem.{contextUniverse2, contextUniverse2} G (@Subgroup.{contextUniverse2} G contextInstance3)
      (@SetLike.instMembership.{contextUniverse2, contextUniverse2} (@Subgroup.{contextUniverse2} G contextInstance3) G
        (@Subgroup.instSetLike.{contextUniverse2} G contextInstance3))
      T x)
  (@Subgroup.mul.{contextUniverse2} G contextInstance3 T)]
    (e : @MonoidAlgebra.{contextUniverse1, contextUniverse2} K G
  (@CommSemiring.toSemiring.{contextUniverse1} K (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance2))))
    (he : @Eq.{max (contextUniverse1 + 1) (contextUniverse2 + 1)}
  (@MonoidAlgebra.{contextUniverse1, contextUniverse2} K G
    (@CommSemiring.toSemiring.{contextUniverse1} K
      (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance2))))
  (@HMul.hMul.{max contextUniverse1 contextUniverse2, max contextUniverse1 contextUniverse2, max contextUniverse1 contextUniverse2}
    (@MonoidAlgebra.{contextUniverse1, contextUniverse2} K G
      (@CommSemiring.toSemiring.{contextUniverse1} K
        (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance2))))
    (@MonoidAlgebra.{contextUniverse1, contextUniverse2} K G
      (@CommSemiring.toSemiring.{contextUniverse1} K
        (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance2))))
    (@MonoidAlgebra.{contextUniverse1, contextUniverse2} K G
      (@CommSemiring.toSemiring.{contextUniverse1} K
        (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance2))))
    (@instHMul.{max contextUniverse1 contextUniverse2}
      (@MonoidAlgebra.{contextUniverse1, contextUniverse2} K G
        (@CommSemiring.toSemiring.{contextUniverse1} K
          (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance2))))
      (@MonoidAlgebra.instMul.{contextUniverse1, contextUniverse2} K G
        (@CommSemiring.toSemiring.{contextUniverse1} K
          (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance2)))
        (@MulOne.toMul.{contextUniverse2} G
          (@MulOneClass.toMulOne.{contextUniverse2} G
            (@Monoid.toMulOneClass.{contextUniverse2} G
              (@DivInvMonoid.toMonoid.{contextUniverse2} G (@Group.toDivInvMonoid.{contextUniverse2} G contextInstance3)))))))
    e e)
  e) : representation T e*representation T e=representation T e := by
  exact ((representation T).map_mul e e).symm.trans (congrArg (representation T) he)
variable {W : Type portUniverse3} {N : Type portUniverse4} [Fintype W] [LinearOrder W] [Fintype N] [LinearOrder N]
variable (hw : Fintype.card W=Fintype.card G)
variable (hn : Fintype.card N=Module.finrank K (LinearMap.range (Algebra.lmul K (MonoidAlgebra K G) e)))
include hexp he hw hn in
lemma greedy_pair : Fintype.card N*Fintype.card (G ⧸ T)=Fintype.card W*Fintype.card (GreedyRing.I (augmentation T) (representation T e)) := by
  apply GreedyRing.pair_dimension (augmentation T) (augmentation_unit T p hexp) (representation T e) (representation_idempotent T e he)
  · rw [(unpack (K := K) T).finrank_eq,Module.finrank_eq_card_basis (MonoidAlgebra.basis G K)]
    exact hw
  · change Fintype.card N=Module.finrank K (LinearMap.range (endomorphism T e))
    rw [endomorphism_rank]
    exact hn

def explicitJ : Matrix W N (Matrix (G ⧸ T) (G ⧸ T) (D (K := K) T)) := fun w n =>
  (Matrix.toLinAlgEquiv' (R := D (K := K) T) (n := G ⧸ T)).symm
    (GreedyRing.rectangleJ (augmentation T) (augmentation_unit T p hexp) (representation T e) (representation_idempotent T e he) (greedy_pair T p hexp e he hw hn) w n)
def explicitY : Matrix N W (Matrix (G ⧸ T) (G ⧸ T) (D (K := K) T)) := fun n w =>
  (Matrix.toLinAlgEquiv' (R := D (K := K) T) (n := G ⧸ T)).symm
    (GreedyRing.rectangleY (augmentation T) (augmentation_unit T p hexp) (representation T e) (representation_idempotent T e he) (greedy_pair T p hexp e he hw hn) n w)
lemma explicit_products :
    explicitY T p hexp e he hw hn*explicitJ T p hexp e he hw hn=1 ∧
    explicitJ T p hexp e he hw hn*explicitY T p hexp e he hw hn=Matrix.diagonal (fun _ : W => representation T e) := by
  let φ := (Matrix.toLinAlgEquiv' (R := D (K := K) T) (n := G ⧸ T)).symm
  have hYJ := GreedyRing.rectangleYJ (augmentation T) (augmentation_unit T p hexp) (representation T e) (representation_idempotent T e he) (greedy_pair T p hexp e he hw hn)
  have hJY := GreedyRing.rectangleJY (augmentation T) (augmentation_unit T p hexp) (representation T e) (representation_idempotent T e he) (greedy_pair T p hexp e he hw hn)
  constructor
  · funext n n'
    have hh := congrArg (fun F => φ (F n n')) hYJ
    simpa only [explicitY,explicitJ,Matrix.mul_apply,map_sum,map_mul,Matrix.one_apply,apply_ite,map_one,map_zero] using hh
  · funext w w'
    have hh := congrArg (fun F => φ (F w w')) hJY
    have hφ : φ (Matrix.toLin' (representation T e))=representation T e :=
      (Matrix.toLinAlgEquiv' (R := D (K := K) T) (n := G ⧸ T)).symm_apply_apply _
    simp only [Matrix.toLin'_apply'] at hh hφ
    simpa only [explicitJ,explicitY,Matrix.mul_apply,map_sum,map_mul,Matrix.diagonal_apply,apply_ite,map_zero,hφ] using hh
end
end OddKaplansky.OrderedCosetMatrix

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.OrderedSectorOrbit
noncomputable section
open scoped Classical BigOperators Matrix
open WreathFourier
variable {K : Type portUniverse1} {H : Type portUniverse2} [Field K] [Group H] [Fintype H] [LinearOrder H]
local instance orderedSectorGreedyDecidableEq : DecidableEq H := Classical.decEq H
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable (hcomm : ∀ r : Rep (H := H) M, ∀ s t : T M r, s*t=t*s)
variable (hexp : ∀ r : Rep (H := H) M, ∀ t : T M r, t^p=1)
variable (e : MonoidAlgebra K H) (he : e*e=e)
variable {W : Type portUniverse3} {N : Type portUniverse4} [Fintype W] [LinearOrder W] [Fintype N] [LinearOrder N]
variable (hw : Fintype.card W = Fintype.card H)
variable (hn : Fintype.card N = Module.finrank K (LinearMap.range (Algebra.lmul K (MonoidAlgebra K H) e)))
def blockJ (r : Rep (H := H) M) : Matrix W N (Block (K := K) M r) := by
  letI : IsMulCommutative (T M r) := ⟨⟨hcomm r⟩⟩
  exact OrderedCosetMatrix.explicitJ (T M r) p (hexp r) e he hw hn
def blockY (r : Rep (H := H) M) : Matrix N W (Block (K := K) M r) := by
  letI : IsMulCommutative (T M r) := ⟨⟨hcomm r⟩⟩
  exact OrderedCosetMatrix.explicitY (T M r) p (hexp r) e he hw hn
lemma block_products (r : Rep (H := H) M) :
    blockY M p hcomm hexp e he hw hn r*blockJ M p hcomm hexp e he hw hn r=1 ∧
    blockJ M p hcomm hexp e he hw hn r*blockY M p hcomm hexp e he hw hn r=Matrix.diagonal (fun _ : W => OrderedCosetMatrix.representation (T M r) e) := by
  let : IsMulCommutative (T M r) := ⟨⟨hcomm r⟩⟩
  have hs := OrderedCosetMatrix.explicit_products (T M r) p (hexp r) e he hw hn
  constructor
  · convert hs.1 using 1 <;> congr ; exact Subsingleton.elim _ _
  · exact hs.2
def explicitJ : Matrix W N (MonoidAlgebra K (Wreath (H := H) M)) := matrixPack M hζ (blockJ M p hcomm hexp e he hw hn)
def explicitY : Matrix N W (MonoidAlgebra K (Wreath (H := H) M)) := matrixPack M hζ (blockY M p hcomm hexp e he hw hn)
variable (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
variable (hm : (Fintype.card (Fourier.C M) : K) ≠ 0)
include hc hm in
lemma explicit_properties :
    explicitY M hζ p hcomm hexp e he hw hn*explicitJ M hζ p hcomm hexp e he hw hn=Matrix.diagonal (fun _ => SectorFourier.f M hζ) ∧
    explicitJ M hζ p hcomm hexp e he hw hn*explicitY M hζ p hcomm hexp e he hw hn=Matrix.diagonal (fun _ => SectorFourier.f M hζ * MonoidAlgebra.mapDomainAlgHom K K (top M) e) ∧
    (∀ w n, SectorFourier.f M hζ * explicitJ M hζ p hcomm hexp e he hw hn w n=explicitJ M hζ p hcomm hexp e he hw hn w n) ∧
    (∀ n w, SectorFourier.f M hζ * explicitY M hζ p hcomm hexp e he hw hn n w=explicitY M hζ p hcomm hexp e he hw hn n w) := by
  have hYJ (r : Rep (H := H) M) := (block_products M p hcomm hexp e he hw hn r).1
  have hJY (r : Rep (H := H) M) := (block_products M p hcomm hexp e he hw hn r).2
  refine ⟨?_,?_,?_,?_⟩
  · rw [explicitY,explicitJ,matrixPack_mul M hζ hc]
    simp only [hYJ]
    convert matrixPack_one M hζ hc hm using 1
  · rw [explicitJ,explicitY,matrixPack_mul M hζ hc]
    simp only [hJY]
    funext w w'
    simp only [matrixPack,Matrix.diagonal_apply]
    by_cases h : w=w'
    · simp only [h,ite_true,pack_representation M hζ hc e hm]
    · simp only [if_neg h]
      exact map_zero _
  · intro w n
    exact pack_left_sector M hζ hc hm _
  · intro n w
    exact pack_left_sector M hζ hc hm _
end
end OddKaplansky.OrderedSectorOrbit

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.OrderedSourceSector
noncomputable section
local instance orderedSourceDecidableEq (α : Type portUniverse1) : DecidableEq α := Classical.decEq α
open scoped Classical BigOperators Matrix
open WreathFourier OrderedSectorOrbit
variable {K : Type} [Field K] (M p : ℕ) [NeZero M] [Fact p.Prime] [CharP K p]
local instance : DecidableEq (SectorStabilizer.H M p) := Classical.decEq _
variable {ζ : K} (hζ : IsPrimitiveRoot ζ M)
lemma stabilizer_comm (r : Rep (H := SectorStabilizer.H M p) M) : ∀ s t : T M r, s*t=t*s := by
  rw [T_leftFixed]
  exact SectorStabilizer.commutative M p (fun x => (lmb M r x).toAdd) (lmb_weight M r)
lemma stabilizer_exp (r : Rep (H := SectorStabilizer.H M p) M) : ∀ t : T M r, t^p=1 := by
  rw [T_leftFixed]
  exact SectorStabilizer.exponent M p (fun x => (lmb M r x).toAdd) (lmb_weight M r)
variable (e : MonoidAlgebra K (SectorStabilizer.H M p)) (he : e*e=e)
variable {W : Type portUniverse2} {N : Type portUniverse3} [Fintype W] [LinearOrder W] [Fintype N] [LinearOrder N]
variable (hw : Fintype.card W=Fintype.card (SectorStabilizer.H M p))
variable (hn : Fintype.card N=Module.finrank K (LinearMap.range (Algebra.lmul K _ e)))
def explicitJ := OrderedSectorOrbit.explicitJ M hζ p (stabilizer_comm M p) (stabilizer_exp M p) e he hw hn
def explicitY := OrderedSectorOrbit.explicitY M hζ p (stabilizer_comm M p) (stabilizer_exp M p) e he hw hn
lemma explicit_properties (hc : (Fintype.card (Base (H := SectorStabilizer.H M p) M) : K) ≠ 0)
    (hm : (Fintype.card (Fourier.C M) : K) ≠ 0) :
    explicitY M p hζ e he hw hn*explicitJ M p hζ e he hw hn=Matrix.diagonal (fun _ => SectorFourier.f M hζ) ∧
    explicitJ M p hζ e he hw hn*explicitY M p hζ e he hw hn=Matrix.diagonal (fun _ => SectorFourier.f M hζ * MonoidAlgebra.mapDomainAlgHom K K (top M) e) ∧
    (∀ w n, SectorFourier.f M hζ * explicitJ M p hζ e he hw hn w n=explicitJ M p hζ e he hw hn w n) ∧
    (∀ n w, SectorFourier.f M hζ * explicitY M p hζ e he hw hn n w=explicitY M p hζ e he hw hn n w) :=
  OrderedSectorOrbit.explicit_properties M hζ p (stabilizer_comm M p) (stabilizer_exp M p) e he hw hn hc hm
end
end OddKaplansky.OrderedSourceSector

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.OrderedSourceSector
noncomputable section
open scoped Classical BigOperators Matrix
open WreathFourier OrderedSectorOrbit
variable (M p : ℕ) [NeZero M] [Fact p.Prime]
variable (r : Rep (H := SectorStabilizer.H M p) M)
local instance : CommGroup (T M r) :=
  { (inferInstance : Group (T M r)) with mul_comm := stabilizer_comm M p r }
variable {K : Type portUniverse1} [Field K] [CharP K p]

variable {S : Type portUniverse2} [Fintype S] [LinearOrder S]
variable (E : Matrix S S (MonoidAlgebra K (T M r)))
variable (hE : E*E=E)
end
end OddKaplansky.OrderedSourceSector

end

end OAI
end

section
namespace OAI

section
namespace OddKaplansky.StarAmalgam
noncomputable section
open Monoid
open scoped Classical
variable {I G : Type} [Group G] {D S : I → Type}
variable [∀ i, Group (D i)] [∀ i, Group (S i)]
variable (f : ∀ i, S i →* G) (g : ∀ i, S i →* D i)
@[elab_as_elim]
theorem induction_on {P : Amalgam f g → Prop} (x : Amalgam f g)
    (hb : ∀ h, P (ofBase f g h)) (hd : ∀ i h, P (ofFactor f g i h))
    (hmul : ∀ x y, P x → P y → P (x*y)) : P x := by
  change ∀ left right : (con f g).Quotient, P left → P right → P (left * right) at hmul
  change ∀ element : G, P ((con f g).mk' (Coprod.inl element)) at hb
  obtain ⟨w,rfl⟩ := (Con.mk'_surjective (c := con f g)) x
  induction w using Coprod.induction_on with
  | inl h => exact hb h
  | inr w =>
    induction w using CoprodI.induction_on with
    | one => simpa only [map_one] using hb 1
    | of i h => exact hd i h
    | mul a b ha hb => simpa only [map_mul] using hmul _ _ ha hb
  | mul a b ha hb => simpa only [map_mul] using hmul _ _ ha hb
lemma base_central (z : G) (hz : ∀ h, Commute z h)
    (a : ∀ i, S i) (ha : ∀ i, f i (a i)=z) (hc : ∀ i h, Commute (g i (a i)) h) :
    ∀ x : Amalgam f g, Commute (ofBase f g z) x := by
  intro x
  induction x using induction_on f g with
  | hb h => exact (hz h).map (ofBase f g)
  | hd i h =>
    rw [← ha i,identify]
    exact (hc i h).map (ofFactor f g i)
  | hmul x y hx hy => exact hx.mul_right hy
instance [Finite I] [∀ i, Finite (D i)] [Group.FG G] : Group.FG (Amalgam f g) := by
  obtain ⟨B,hB,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let C : Set (Amalgam f g) := ofBase f g '' B ∪ Set.range (fun z : (i : I) × D i => ofFactor f g z.1 z.2)
  apply Group.fg_iff.mpr
  refine ⟨C,?_,(hfin.image _).union (Set.finite_range _)⟩
  apply top_unique
  intro x hxTop
  clear hxTop
  induction x using induction_on f g with
  | hb h =>
    have hh : h ∈ Subgroup.closure B := hB ▸ Subgroup.mem_top h
    induction hh using Subgroup.closure_induction with
    | mem h hh => exact Subgroup.subset_closure (Or.inl ⟨h,hh,rfl⟩)
    | one => simp only [map_one, one_mem]
    | mul h k _ _ hh hk => simpa only [map_mul] using (Subgroup.closure C).mul_mem hh hk
    | inv h _ hh => simpa only [map_inv] using (Subgroup.closure C).inv_mem hh
  | hd i h => exact Subgroup.subset_closure (Or.inr ⟨⟨i,h⟩,rfl⟩)
  | hmul x y hx hy => exact (Subgroup.closure C).mul_mem hx hy
end
end OddKaplansky.StarAmalgam

end

end OAI
end

section
namespace OAI

section
namespace OddKaplansky.SectorGroup
noncomputable section
open scoped Classical BigOperators
open WreathFourier
variable {I G₀ H : Type} [sectionInstance66 : Fintype I] [Group G₀] [Group H] [sectionInstance67 : Fintype H]
variable (M : ℕ) [sectionInstance68 : NeZero M] (i : I → (H →* G₀))
abbrev Attached := Wreath (H := H) M
abbrev Common := Fourier.C M × H
def toBase (j : I) : Common (H := H) M →* (Fourier.C M × G₀) :=
  (MonoidHom.id (Fourier.C M)).prodMap (i j)
def toAttached (_j : I) : Common (H := H) M →* Attached (H := H) M where
  toFun a := ⟨fun _ => a.1,a.2⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp only [Prod.fst_mul, toAdd_mul, RegularWreathProduct.mul_left, Pi.mul_apply, Prod.snd_mul, RegularWreathProduct.mul_right]
lemma toBase_injective
    {I : Type}
    {G₀ : Type}
    {H : Type}
    [Fintype.{0} I]
    [contextInstance4 : Group.{0} G₀]
    [contextInstance5 : Group.{0} H]
    [Fintype.{0} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    (i : I →
  @MonoidHom.{0, 0} H G₀
    (@MulOneClass.toMulOne.{0} H
      (@Monoid.toMulOneClass.{0} H (@DivInvMonoid.toMonoid.{0} H (@Group.toDivInvMonoid.{0} H contextInstance5))))
    (@MulOneClass.toMulOne.{0} G₀
      (@Monoid.toMulOneClass.{0} G₀ (@DivInvMonoid.toMonoid.{0} G₀ (@Group.toDivInvMonoid.{0} G₀ contextInstance4))))) (hi : ∀ j, Function.Injective (i j)) (j : I) : Function.Injective (toBase M i j) := by
  intro a b he
  change (a.1,i j a.2)=(b.1,i j b.2) at he
  exact Prod.ext (congrArg (fun x : Fourier.C M × G₀ => x.1) he) (hi j (congrArg (fun x : Fourier.C M × G₀ => x.2) he))
lemma toAttached_injective
    {I : Type}
    {H : Type}
    [Fintype.{0} I]
    [Group.{0} H]
    [Fintype.{0} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (j : I) : Function.Injective (toAttached (H := H) M j) := by
  intro a b he
  exact Prod.ext (congrArg (fun g : Attached (H := H) M => g.left 1) he) (congrArg RegularWreathProduct.right he)
abbrev G₁ := StarAmalgam.Amalgam (toBase M i) (toAttached (H := H) M)
def base : (Fourier.C M × G₀) →* G₁ M i := StarAmalgam.ofBase (toBase M i) (toAttached (H := H) M)
def factor (j : I) : Attached (H := H) M →* G₁ M i := StarAmalgam.ofFactor (toBase M i) (toAttached (H := H) M) j
def original : G₀ →* G₁ M i := (base M i).comp (MonoidHom.inr _ _)
def central : Fourier.C M →* G₁ M i := (base M i).comp (MonoidHom.inl _ _)
lemma base_injective (hi : ∀ j, Function.Injective (i j)) : Function.Injective (base M i) :=
  StarAmalgam.ofBase_injective _ _ (toBase_injective M i hi) (toAttached_injective M)
lemma central_injective (hi : ∀ j, Function.Injective (i j)) : Function.Injective (central M i) := by
  intro a b he
  exact congrArg Prod.fst (base_injective M i hi he)
lemma identify_top
    {I : Type}
    {G₀ : Type}
    {H : Type}
    [Fintype.{0} I]
    [contextInstance4 : Group.{0} G₀]
    [contextInstance5 : Group.{0} H]
    [Fintype.{0} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    (i : I →
  @MonoidHom.{0, 0} H G₀
    (@MulOneClass.toMulOne.{0} H
      (@Monoid.toMulOneClass.{0} H (@DivInvMonoid.toMonoid.{0} H (@Group.toDivInvMonoid.{0} H contextInstance5))))
    (@MulOneClass.toMulOne.{0} G₀
      (@Monoid.toMulOneClass.{0} G₀ (@DivInvMonoid.toMonoid.{0} G₀ (@Group.toDivInvMonoid.{0} G₀ contextInstance4))))) (j : I) (h : H) : original M i (i j h) = factor M i j (top M h) := by
  convert StarAmalgam.identify (toBase M i) (toAttached (H := H) M) j (1,h) using 1 <;> rfl
lemma identify_diagonal
    {I : Type}
    {G₀ : Type}
    {H : Type}
    [Fintype.{0} I]
    [contextInstance4 : Group.{0} G₀]
    [contextInstance5 : Group.{0} H]
    [Fintype.{0} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    (i : I →
  @MonoidHom.{0, 0} H G₀
    (@MulOneClass.toMulOne.{0} H
      (@Monoid.toMulOneClass.{0} H (@DivInvMonoid.toMonoid.{0} H (@Group.toDivInvMonoid.{0} H contextInstance5))))
    (@MulOneClass.toMulOne.{0} G₀
      (@Monoid.toMulOneClass.{0} G₀ (@DivInvMonoid.toMonoid.{0} G₀ (@Group.toDivInvMonoid.{0} G₀ contextInstance4))))) (j : I) (c : Fourier.C M) : central M i c = factor M i j (SectorFourier.diagonal M c) := by
  simpa only [central, base, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply, factor, SectorFourier.diagonal, WreathFourier.base, SectorFourier.constant, MonoidHom.coe_mk, OneHom.coe_mk, toBase, MonoidHom.coe_prodMap, MonoidHom.coe_id, Prod.map_apply, id_eq, map_one, toAttached] using StarAmalgam.identify (toBase M i) (toAttached (H := H) M) j (c,1)
lemma central_commute
    {I : Type}
    {G₀ : Type}
    {H : Type}
    [Fintype.{0} I]
    [contextInstance4 : Group.{0} G₀]
    [contextInstance5 : Group.{0} H]
    [Fintype.{0} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    (i : I →
  @MonoidHom.{0, 0} H G₀
    (@MulOneClass.toMulOne.{0} H
      (@Monoid.toMulOneClass.{0} H (@DivInvMonoid.toMonoid.{0} H (@Group.toDivInvMonoid.{0} H contextInstance5))))
    (@MulOneClass.toMulOne.{0} G₀
      (@Monoid.toMulOneClass.{0} G₀ (@DivInvMonoid.toMonoid.{0} G₀ (@Group.toDivInvMonoid.{0} G₀ contextInstance4))))) (c : Fourier.C M) (g : G₁ M i) : Commute (central M i c) g := by
  exact StarAmalgam.base_central (toBase M i) (toAttached (H := H) M) (c,1)
    (fun h => by change (c,1)*h=h*(c,1); ext <;> simp only [Prod.fst_mul, toAdd_mul, mul_comm, Prod.snd_mul, one_mul, mul_one])
    (fun _ => (c,1)) (fun j => by simp only [toBase, MonoidHom.coe_prodMap, MonoidHom.coe_id, Prod.map_apply, id_eq, map_one])
    (fun j h => SectorFourier.diagonal_central M c h) g
instance [Group.FG G₀] : Group.FG (G₁ M i) := inferInstance
variable {K : Type} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
def f : MonoidAlgebra K (G₁ M i) := CharacterIdempotents.pushed (central M i) (Fourier.cyclicCharacter M hζ)
lemma f_idempotent
    {I : Type}
    {G₀ : Type}
    {H : Type}
    [Fintype.{0} I]
    [contextInstance4 : Group.{0} G₀]
    [contextInstance5 : Group.{0} H]
    [Fintype.{0} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    (i : I →
  @MonoidHom.{0, 0} H G₀
    (@MulOneClass.toMulOne.{0} H
      (@Monoid.toMulOneClass.{0} H (@DivInvMonoid.toMonoid.{0} H (@Group.toDivInvMonoid.{0} H contextInstance5))))
    (@MulOneClass.toMulOne.{0} G₀
      (@Monoid.toMulOneClass.{0} G₀ (@DivInvMonoid.toMonoid.{0} G₀ (@Group.toDivInvMonoid.{0} G₀ contextInstance4)))))
    {K : Type}
    [contextInstance11 : Field.{0} K]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{0} K (@CommRing.toCommMonoid.{0} K (@Field.toCommRing.{0} K contextInstance11)) ζ M) (hm : (Fintype.card (Fourier.C M) : K) ≠ 0) : f M i hζ * f M i hζ=f M i hζ :=
  CharacterIdempotents.pushed_idempotent _ _ hm
lemma f_ne_zero (hi : ∀ j, Function.Injective (i j)) (hm : (Fintype.card (Fourier.C M) : K) ≠ 0) : f M i hζ ≠ 0 :=
  CharacterIdempotents.pushed_ne_zero _ (central_injective M i hi) _ hm
lemma f_central (a : MonoidAlgebra K (G₁ M i)) : Commute (f M i hζ) a :=
  CharacterIdempotents.pushed_central _ _ (central_commute M i) a
lemma factor_f (j : I) : MonoidAlgebra.mapDomainAlgHom K K (factor M i j) (SectorFourier.f M hζ) = f M i hζ := by
  have he : (factor M i j).comp (SectorFourier.diagonal M) = central M i := MonoidHom.ext (fun c => (identify_diagonal M i j c).symm)
  simp only [SectorFourier.f,f,CharacterIdempotents.pushed,] at *
  rw [← AlgHom.comp_apply,← MonoidAlgebra.mapDomainAlgHom_comp,he]
lemma factor_original (j : I) (e : MonoidAlgebra K H) :
    MonoidAlgebra.mapDomainAlgHom K K (factor M i j) (MonoidAlgebra.mapDomainAlgHom K K (top M) e) =
      MonoidAlgebra.mapDomainAlgHom K K (original M i) (MonoidAlgebra.mapDomainAlgHom K K (i j) e) := by
  have he : (factor M i j).comp (top M) = (original M i).comp (i j) := MonoidHom.ext (fun h => (identify_top M i j h).symm)
  rw [← AlgHom.comp_apply,← MonoidAlgebra.mapDomainAlgHom_comp,he,MonoidAlgebra.mapDomainAlgHom_comp,AlgHom.comp_apply]
end
end OddKaplansky.SectorGroup

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.NilpotentBasis
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {R : Type portUniverse2} [Field K] [Ring R] [Algebra K R]
variable (p : ℕ) (X : R) (b : Module.Basis (Fin p) K R)
variable (hb : ∀ i : Fin p, b i = X^i.val) (hX : X^p=0)
include hb hX in
lemma coeff_power (n : ℕ) (j : Fin p) : b.repr (X^n) j = if n=j.val then 1 else 0 := by
  by_cases hn : n<p
  · rw [← hb ⟨n,hn⟩]
    simp only [Module.Basis.repr_self,Finsupp.single_apply]
    congr 1
    exact propext Fin.ext_iff
  · rw [pow_eq_zero_of_le (by omega : p≤n) hX,map_zero,Finsupp.zero_apply,if_neg (by omega)]
include hb hX in
lemma low_coefficient (ell : ℕ) (a : R) (ha : a*X^ell=0) (i : Fin p) (hi : i.val+ell<p) :
    b.repr a i=0 := by
  have hh := congrArg (fun v : R => b.repr v ⟨i.val+ell,hi⟩) ha
  rw [← b.sum_repr a,Finset.sum_mul] at hh
  have hstep (j : Fin p) : b.repr ((b.repr a j • b j) * X^ell) ⟨i.val+ell,hi⟩ =
      if j=i then b.repr a j else 0 := by
    rw [hb,smul_mul_assoc,← pow_add,map_smul,Finsupp.smul_apply,coeff_power p X b hb hX]
    simp only [Nat.add_right_cancel_iff,Fin.val_inj,smul_eq_mul,mul_ite,mul_one,mul_zero]
  simp only [map_sum,Finset.sum_apply',hstep,map_zero,Finsupp.zero_apply,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hh
  exact hh
include hb hX in
lemma right_divisible (ell : ℕ) (hell : ell≤p) (a : R) (ha : a*X^ell=0) :
    ∃ q : R, a=q*X^(p-ell) := by
  refine ⟨∑ i : Fin p, b.repr a i • X^(i.val-(p-ell)),?_⟩
  rw [Finset.sum_mul]
  conv_lhs => rw [← b.sum_repr a]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : p - ell ≤ i.val
  · rw [smul_mul_assoc,← pow_add,Nat.sub_add_cancel hi,← hb]
  · have hz := low_coefficient p X b hb hX ell a ha i (by omega)
    rw [hz,zero_smul,zero_smul,zero_mul]
end
end OddKaplansky.NilpotentBasis

namespace OddKaplansky.CyclicAlgebra
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse3} [Field K]
variable (p : ℕ) [Fact p.Prime] [sectionInstance69 : CharP K p]
abbrev C := Multiplicative (ZMod p)
abbrev R := MonoidAlgebra K (C p)
def gen : C p := Multiplicative.ofAdd 1
def X : R (K := K) p := MonoidAlgebra.single (gen p) 1-1
instance : CharP (R (K := K) p) p := CharP.of_ringHom_of_ne_zero (algebraMap K _) p (Fact.out : p.Prime).ne_zero
lemma gen_pow : gen p ^ p =1 := by apply Multiplicative.toAdd.injective; simp only [gen, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one, toAdd_one]
lemma nilpotent : X (K := K) p ^ p=0 := by
  rw [X,sub_pow_char,MonoidAlgebra.single_pow,gen_pow,one_pow,one_pow,← MonoidAlgebra.one_def,sub_self]
lemma gen_val (g : C p) : gen p ^ g.toAdd.val = g := by
  apply Multiplicative.toAdd.injective
  simp only [gen, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id', id_eq, mul_one]
lemma delta_binomial
    {K : Type contextUniverse1}
    [contextInstance1 : Field.{contextUniverse1} K]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance1))))
  p] (g : C p) : MonoidAlgebra.single g (1 : K) = (X p+1)^g.toAdd.val := by
  rw [X,sub_add_cancel,MonoidAlgebra.single_pow,one_pow,gen_val]
lemma spanning : ⊤ ≤ Submodule.span K (Set.range (fun i : Fin p => X (K := K) p ^ i.val)) := by
  intro a
  have hi : a ∈ Submodule.span K (Set.range (fun i : Fin p => X (K := K) p ^ i.val)) := by
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      rw [MonoidAlgebra.of_apply,delta_binomial,add_pow]
      apply Submodule.sum_mem
      intro k hk
      simp only [one_pow,mul_one]
      rw [mul_comm,← nsmul_eq_mul]
      apply (Submodule.span K (Set.range (fun i : Fin p => X (K := K) p ^ i.val))).toAddSubmonoid.nsmul_mem
      apply Submodule.subset_span
      exact ⟨⟨k,lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) (ZMod.val_lt g.toAdd)⟩,rfl⟩
    | add a b ha hb => exact Submodule.add_mem _ ha hb
    | smul c a ha => exact Submodule.smul_mem _ c ha
  exact fun _ => hi
lemma independent : LinearIndependent K (fun i : Fin p => X (K := K) p ^ i.val) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank (spanning p)
  rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis (C p) K)]
  simp only [Fintype.card_fin, C, Fintype.card_multiplicative, ZMod.card]
def basis : Module.Basis (Fin p) K (R (K := K) p) := Module.Basis.mk (independent p) (spanning p)
lemma basis_apply (i : Fin p) : basis (K := K) p i = X p^i.val := Module.Basis.mk_apply _ _ _
lemma right_divisible (ell : ℕ) (hell : ell≤p) (a : R (K := K) p) (ha : a*X p^ell=0) :
    ∃ q, a=q*X p^(p-ell) := NilpotentBasis.right_divisible (K := K) p (X p) (basis p) (basis_apply p) (nilpotent p) ell hell a ha
end
end OddKaplansky.CyclicAlgebra

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.CosetMatrix
noncomputable section
open scoped Classical BigOperators
open CosetCoordinates
variable {K : Type portUniverse1} {G : Type portUniverse2} [Field K] [Group G] [sectionInstance70 : Fintype G] (T : Subgroup G)
lemma mk_right
    {G : Type contextUniverse1}
    [contextInstance1 : Group.{contextUniverse1} G]
    [Fintype.{contextUniverse1} G]
    (T : @Subgroup.{contextUniverse1} G contextInstance1) (g : G) (t : T) : ((g*t : G) : G ⧸ T) = (g : G ⧸ T) :=
  QuotientGroup.mk_mul_of_mem _ t.property
lemma residue_right (g : G) (t : T) : residue T (g*t) = residue T g * t := by
  apply Subtype.ext
  simp only [residue,mk_right,Subgroup.coe_mul,mul_assoc]
lemma unpack_right_single (v : (G ⧸ T) → D (K := K) T) (t : T) :
    unpack T (fun q => v q * MonoidAlgebra.single t 1) =
      unpack T v * MonoidAlgebra.single (t : G) 1 := by
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [unpack_coeff,MonoidAlgebra.coeff_mul_single_apply,MonoidAlgebra.coeff_mul_single_apply,
    unpack_coeff,mul_one,mul_one]
  simp only [← Subgroup.coe_inv,mk_right,residue_right]
lemma unpack_right (v : (G ⧸ T) → D (K := K) T) (b : D (K := K) T) :
    unpack T (fun q => v q * b) = unpack T v * MonoidAlgebra.mapDomainAlgHom K K T.subtype b := by
  induction b using MonoidAlgebra.induction_on with
  | of t =>
    convert unpack_right_single T v t using 1 <;> simp only [MonoidAlgebra.of_apply, MonoidAlgebra.mapDomainAlgHom_apply, Subgroup.coe_subtype, MonoidAlgebra.mapDomain_single]
  | add b c hb hc =>
    simp only [mul_add,map_add]
    change unpack T ((fun q => v q*b)+(fun q => v q*c)) = _
    rw [map_add,hb,hc]
  | smul c b hb =>
    simp only [mul_smul_comm,map_smul]
    change unpack T (c • (fun q => v q*b)) = _
    rw [map_smul,hb]
lemma right_divisible (X : D (K := K) T) (n k : ℕ)
    (hdiv : ∀ a : D (K := K) T, a*X^n=0 → ∃ b, a=b*X^k)
    (a : MonoidAlgebra K G) (ha : a*(MonoidAlgebra.mapDomainAlgHom K K T.subtype X)^n=0) :
    ∃ b, a=b*(MonoidAlgebra.mapDomainAlgHom K K T.subtype X)^k := by
  let v := (unpack (K := K) T).symm a
  have hv : ∀ q, v q * X^n=0 := by
    have hh : unpack T (fun q => v q*X^n)=0 := by
      rw [unpack_right,map_pow,LinearEquiv.apply_symm_apply,ha]
    have hz := (unpack T).injective (hh.trans (map_zero (unpack T)).symm)
    exact fun q => congrFun hz q
  choose w hw using fun q => hdiv (v q) (hv q)
  refine ⟨unpack T w,?_⟩
  rw [← map_pow,← unpack_right]
  exact (LinearEquiv.apply_symm_apply (unpack T) a).symm.trans (congrArg (unpack T) (funext hw))
end
end OddKaplansky.CosetMatrix

namespace OddKaplansky.CyclicAlgebra
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse3} {G : Type portUniverse4} [Field K] [Group G] [Fintype G]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
lemma embedded_right_divisible (i : C p →* G) (hi : Function.Injective i)
    (ell : ℕ) (hell : ell≤p) (a : MonoidAlgebra K G)
    (ha : a*(MonoidAlgebra.single (i (gen p)) 1-1)^ell=0) :
    ∃ b, a=b*(MonoidAlgebra.single (i (gen p)) 1-1)^(p-ell) := by
  let φ := MonoidAlgebra.domCongr K K (MonoidHom.ofInjective hi)
  let Xi := φ (X (K := K) p)
  have hXi : MonoidAlgebra.mapDomainAlgHom K K i.range.subtype Xi =
      MonoidAlgebra.single (i (gen p)) (1 : K)-1 := by
    simp only [Xi,φ,X,map_sub,map_one,MonoidAlgebra.domCongr_single]
    simp only [MonoidAlgebra.mapDomainAlgHom_apply,MonoidAlgebra.mapDomain_single]
    rfl
  apply CosetMatrix.right_divisible i.range Xi ell (p-ell) _ a (by rwa [hXi]) |>.imp (fun b hb => by rwa [hXi] at hb)
  intro c hc
  have hcz : φ.symm c * X p^ell=0 := by
    apply φ.injective
    simpa only [map_mul,map_pow,AlgEquiv.apply_symm_apply,map_zero] using hc
  obtain ⟨b,hb⟩ := right_divisible p ell hell (φ.symm c) hcz
  refine ⟨φ b,?_⟩
  have hh := congrArg φ hb
  simpa only [map_mul,map_pow,AlgEquiv.apply_symm_apply] using hh
end
end OddKaplansky.CyclicAlgebra

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.OrderedZero
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {A : Type portUniverse2} {B : Type portUniverse3} {G : Type portUniverse4} [Field K] [Group A] [Group B] [Group G] [Fintype A]
variable (p ell : ℕ) [Fact p.Prime] [CharP K p]
lemma product_zero (hell : ell ≤ p-ell)
    (i : CyclicAlgebra.C p →* A) (hi : Function.Injective i)
    (j : CyclicAlgebra.C p →* B) (φ : A →* G) (ψ : B →* G)
    (hij : φ (i (CyclicAlgebra.gen p)) = ψ (j (CyclicAlgebra.gen p)))
    (a : MonoidAlgebra K A) (b : MonoidAlgebra K B)
    (ha : a*(MonoidAlgebra.single (i (CyclicAlgebra.gen p)) 1-1)^ell=0)
    (hb : (MonoidAlgebra.single (j (CyclicAlgebra.gen p)) 1-1)^ell*b=0) :
    MonoidAlgebra.mapDomainAlgHom K K φ a * MonoidAlgebra.mapDomainAlgHom K K ψ b=0 := by
  let Φ := MonoidAlgebra.mapDomainAlgHom K K φ
  let Ψ := MonoidAlgebra.mapDomainAlgHom K K ψ
  let X : MonoidAlgebra K G := MonoidAlgebra.single (φ (i (CyclicAlgebra.gen p))) 1-1
  obtain ⟨c,hc⟩ := CyclicAlgebra.embedded_right_divisible p i hi ell (by omega) a ha
  have hm : Φ (MonoidAlgebra.single (i (CyclicAlgebra.gen p)) 1-1)=X := by rw [map_sub,map_one]; simp only [Φ,X,MonoidAlgebra.mapDomainAlgHom_apply,MonoidAlgebra.mapDomain_single]
  have hn : Ψ (MonoidAlgebra.single (j (CyclicAlgebra.gen p)) 1-1)=X := by rw [map_sub,map_one]; simp only [Ψ,X,MonoidAlgebra.mapDomainAlgHom_apply,MonoidAlgebra.mapDomain_single,hij]
  have hb' : X^ell*Ψ b=0 := by
    have hh := congrArg Ψ hb
    simpa only [map_mul,map_pow,hn,map_zero] using hh
  change Φ a*Ψ b=0
  rw [hc,map_mul,map_pow,hm,mul_assoc]
  have hp : p-ell = (p-ell-ell)+ell := by omega
  rw [hp,pow_add,mul_assoc,hb',mul_zero,mul_zero]
end
end OddKaplansky.OrderedZero

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.Compression
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {R : Type portUniverse2} {I : Type portUniverse3} {T : Type portUniverse4} {W : Type portUniverse5} {N : Type portUniverse6} [Field K] [Ring R] [Algebra K R]
variable [sectionInstance71 : Fintype I] [sectionInstance72 : Fintype T] [sectionInstance74 : Fintype W] [sectionInstance73 : Fintype N]
lemma nilpotent_lower {S : Type portUniverse7} [Ring S] {n : ℕ} (ix : I → Fin n)
    (A : Matrix I I S) (hA : ∀ i j, (ix i).val ≤ (ix j).val → A i j=0) : A^n=0 := by
  have hp (k : ℕ) : ∀ i j, (ix i).val < (ix j).val+k → (A^k) i j=0 := by
    induction k with
    | zero =>
      intro i j h
      have hij : i≠j := by intro he; subst j; omega
      simp only [pow_zero, ne_eq, hij, not_false_eq_true, Matrix.one_apply_ne]
    | succ k ih =>
      intro i j h
      rw [pow_succ',Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro a _
      by_cases ha : (ix a).val < (ix j).val+k
      · rw [ih a j ha,mul_zero]
      · rw [hA i a (by omega),zero_mul]
  funext i j
  exact hp n i j (by have := (ix i).isLt; omega)

def C₀ (P : I → R) (β : I → T → K) : Matrix T I R := fun t i => β i t • P i
def D₀ (P : I → R) (α : I → T → K) : Matrix I T R := fun i t => α i t • P i
lemma D₀C₀
    {K : Type contextUniverse1}
    {R : Type contextUniverse2}
    {I : Type contextUniverse3}
    {T : Type contextUniverse4}
    [contextInstance4 : Field.{contextUniverse1} K]
    [contextInstance5 : Ring.{contextUniverse2} R]
    [@Algebra.{contextUniverse1, contextUniverse2} K R (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance4))
  (@Ring.toSemiring.{contextUniverse2} R contextInstance5)]
    [Fintype.{contextUniverse3} I]
    [Fintype.{contextUniverse4} T] (P : I → R) (α β : I → T → K) (i j : I) :
    (D₀ P α * C₀ P β) i j = (∑ t, α i t*β j t) • (P i*P j) := by
  simp only [Matrix.mul_apply,D₀,C₀,smul_mul_assoc,mul_smul_comm,smul_smul,Finset.sum_smul,mul_comm]
lemma diag_idempotent (P : I → R) (hP : ∀ i, P i*P i=P i) :
    Matrix.diagonal P * Matrix.diagonal P = Matrix.diagonal P := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact hP i
lemma C₀_diag
    {K : Type contextUniverse1}
    {R : Type contextUniverse2}
    {I : Type contextUniverse3}
    {T : Type contextUniverse4}
    [contextInstance4 : Field.{contextUniverse1} K]
    [contextInstance5 : Ring.{contextUniverse2} R]
    [@Algebra.{contextUniverse1, contextUniverse2} K R (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance4))
  (@Ring.toSemiring.{contextUniverse2} R contextInstance5)]
    [Fintype.{contextUniverse3} I]
    [Fintype.{contextUniverse4} T] (P : I → R) (hP : ∀ i, P i*P i=P i) (β : I → T → K) :
    C₀ P β * Matrix.diagonal P = C₀ P β := by
  funext t i
  simp only [Matrix.mul_diagonal,C₀,smul_mul_assoc,hP]
lemma diag_D₀
    {K : Type contextUniverse1}
    {R : Type contextUniverse2}
    {I : Type contextUniverse3}
    {T : Type contextUniverse4}
    [contextInstance4 : Field.{contextUniverse1} K]
    [contextInstance5 : Ring.{contextUniverse2} R]
    [@Algebra.{contextUniverse1, contextUniverse2} K R (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance4))
  (@Ring.toSemiring.{contextUniverse2} R contextInstance5)]
    [Fintype.{contextUniverse3} I]
    [Fintype.{contextUniverse4} T] (P : I → R) (hP : ∀ i, P i*P i=P i) (α : I → T → K) :
    Matrix.diagonal P * D₀ P α = D₀ P α := by
  funext i t
  simp only [Matrix.diagonal_mul,D₀,mul_smul_comm,hP]

def error (P : I → R) (α β : I → T → K) : Matrix I I R := D₀ P α * C₀ P β - Matrix.diagonal P
def correction (P : I → R) (α β : I → T → K) : Matrix I I R :=
  (∑ k ∈ Finset.range (Fintype.card I), (-error P α β)^k) * Matrix.diagonal P
def D₁ (P : I → R) (α β : I → T → K) : Matrix I T R := correction P α β * D₀ P α
lemma corrected (P : I → R) (hP : ∀ i, P i*P i=P i) (α β : I → T → K)
    (ix : I → Fin (Fintype.card I)) (hix : Function.Injective ix)
    (hdiag : ∀ i, ∑ t, α i t*β i t=1)
    (hupper : ∀ i j, (ix i).val < (ix j).val → (∑ t, α i t*β j t) • (P i*P j)=0) :
    D₁ P α β * C₀ P β = Matrix.diagonal P := by
  let E := error P α β
  let Q := Matrix.diagonal P
  have hQ : Q*Q=Q := diag_idempotent P hP
  have hEQ : E*Q=E := by
    dsimp [E,Q,error]
    rw [sub_mul,Matrix.mul_assoc,C₀_diag P hP,diag_idempotent P hP]
  have hQE : Q*E=E := by
    dsimp [E,Q,error]
    rw [mul_sub,← Matrix.mul_assoc,diag_D₀ P hP,diag_idempotent P hP]
  have hnil : E^(Fintype.card I)=0 := by
    apply nilpotent_lower ix E
    intro i j hij
    dsimp [E,error]
    rw [D₀C₀]
    by_cases he : i=j
    · subst j
      simp only [hdiag, hP, one_smul, Matrix.diagonal_apply_eq, sub_self]
    · rw [Matrix.diagonal_apply_ne _ he,sub_zero]
      apply hupper i j
      have hne : (ix i).val ≠ (ix j).val := fun h => he (hix (Fin.ext h))
      omega
  have hgeom : (∑ k ∈ Finset.range (Fintype.card I), (-E)^k) * (1+E)=1 := by
    have hh := geom_sum_mul (-E) (Fintype.card I)
    have hn : (-E)^(Fintype.card I)=0 := by rw [neg_pow,hnil,mul_zero]
    rw [hn] at hh
    have hm : -(1+E)= -E-1 := by noncomm_ring
    rw [← hm,mul_neg] at hh
    have := congrArg Neg.neg hh
    simpa only [neg_neg,zero_sub,neg_neg] using this
  unfold D₁ correction
  change ((∑ k ∈ Finset.range (Fintype.card I), (-E)^k)*Q*D₀ P α)*C₀ P β=Q
  rw [Matrix.mul_assoc,show D₀ P α*C₀ P β=Q+E by dsimp [E,Q,error]; abel]
  have hh : Q*(Q+E)=(1+E)*Q := by rw [mul_add,hQ,hQE,add_mul,one_mul,hEQ]
  rw [mul_assoc,hh,← mul_assoc,hgeom,one_mul]

def rep {A : Type portUniverse8} {B : Type portUniverse9} (X : Matrix A B R) : Matrix (W×A) (W×B) R := fun a b => if a.1=b.1 then X a.2 b.2 else 0
lemma rep_mul {A : Type portUniverse10} {B : Type portUniverse11} {C : Type portUniverse12} [Fintype B] (X : Matrix A B R) (Y : Matrix B C R) :
    rep (W := W) (X*Y)=
      (rep X : Matrix (W×A) (W×B) R) * (rep Y : Matrix (W×B) (W×C) R) := by
  funext a c
  simp only [rep,Matrix.mul_apply,Fintype.sum_prod_type]
  by_cases he : a.1=c.1
  · simp only [he, ↓reduceIte, mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ]
  · simp only [he, ↓reduceIte, mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ]
def blockJ (J : I → Matrix W N R) : Matrix (W×I) (I×N) R := fun a b => if a.2=b.1 then J a.2 a.1 b.2 else 0
def blockY (Y : I → Matrix N W R) : Matrix (I×N) (W×I) R := fun a b => if a.1=b.2 then Y a.1 a.2 b.1 else 0
lemma blockYJ
    {R : Type contextUniverse1}
    {I : Type contextUniverse2}
    {W : Type contextUniverse3}
    {N : Type contextUniverse4}
    [Ring.{contextUniverse1} R]
    [Fintype.{contextUniverse2} I]
    [Fintype.{contextUniverse3} W]
    [Fintype.{contextUniverse4} N] (f : R) (J : I → Matrix W N R) (Y : I → Matrix N W R)
    (hYJ : ∀ i, Y i*J i=Matrix.diagonal (fun _ => f)) : blockY Y*blockJ J=Matrix.diagonal (fun _ => f) := by
  funext a b
  simp only [Matrix.mul_apply,blockY,blockJ,Fintype.sum_prod_type]
  by_cases he : a.1=b.1
  · simp only [← he,ite_mul,zero_mul,mul_ite,mul_zero,]
    have hh := congrFun (congrFun (hYJ a.1) a.2) b.2
    simpa only [he, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Matrix.diagonal_apply, Prod.ext_iff, true_and, Matrix.mul_apply] using hh
  · simp only [mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, he, Finset.sum_const_zero, ne_eq, Prod.ext_iff, false_and, not_false_eq_true, Matrix.diagonal_apply_ne]
lemma blockJY
    {R : Type contextUniverse1}
    {I : Type contextUniverse2}
    {W : Type contextUniverse3}
    {N : Type contextUniverse4}
    [Ring.{contextUniverse1} R]
    [Fintype.{contextUniverse2} I]
    [Fintype.{contextUniverse3} W]
    [Fintype.{contextUniverse4} N] (P : I → R) (J : I → Matrix W N R) (Y : I → Matrix N W R)
    (hJY : ∀ i, J i*Y i=Matrix.diagonal (fun _ => P i)) : blockJ J*blockY Y=rep (Matrix.diagonal P) := by
  funext a b
  simp only [Matrix.mul_apply,blockY,blockJ,Fintype.sum_prod_type,rep]
  by_cases he : a.2=b.2
  · simp only [← he,ite_mul,zero_mul,mul_ite,mul_zero,Finset.sum_ite_irrel,]
    have hh := congrFun (congrFun (hJY a.2) a.1) b.1
    simpa only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Matrix.diagonal_apply_eq, Matrix.mul_apply, Matrix.diagonal_apply] using hh
  · simp only [mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, he, ne_eq, not_false_eq_true, Matrix.diagonal_apply_ne, ite_self]
def Csharp (P : I → R) (β : I → T → K) (J : I → Matrix W N R) : Matrix (W×T) (I×N) R :=
  (rep (C₀ P β) : Matrix (W×T) (W×I) R) * (blockJ J : Matrix (W×I) (I×N) R)
def Dsharp (P : I → R) (α β : I → T → K) (Y : I → Matrix N W R) : Matrix (I×N) (W×T) R :=
  (blockY Y : Matrix (I×N) (W×I) R) * (rep (D₁ P α β) : Matrix (W×I) (W×T) R)
lemma compressed (f : R) (hf : f*f=f)
    (P : I → R) (hP : ∀ i, P i*P i=P i) (α β : I → T → K)
    (ix : I → Fin (Fintype.card I)) (hix : Function.Injective ix)
    (hdiag : ∀ i, ∑ t, α i t*β i t=1)
    (hupper : ∀ i j, (ix i).val < (ix j).val → (∑ t, α i t*β j t) • (P i*P j)=0)
    (J : I → Matrix W N R) (Y : I → Matrix N W R)
    (hYJ : ∀ i, Y i*J i=Matrix.diagonal (fun _ => f))
    (hJY : ∀ i, J i*Y i=Matrix.diagonal (fun _ => P i)) :
    Dsharp P α β Y * Csharp P β J = Matrix.diagonal (fun _ => f) := by
  unfold Dsharp Csharp
  rw [Matrix.mul_assoc,← Matrix.mul_assoc (rep (D₁ P α β)),← rep_mul,corrected P hP α β ix hix hdiag hupper]
  rw [← blockJY P J Y hJY]
  calc
    blockY Y * ((blockJ J*blockY Y)*blockJ J) = (blockY Y*blockJ J)*(blockY Y*blockJ J) := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [blockYJ f J Y hYJ,Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact hf

lemma Csharp_sector
    {K : Type contextUniverse1}
    {R : Type contextUniverse2}
    {I : Type contextUniverse3}
    {T : Type contextUniverse4}
    {W : Type contextUniverse5}
    {N : Type contextUniverse6}
    [contextInstance6 : Field.{contextUniverse1} K]
    [contextInstance7 : Ring.{contextUniverse2} R]
    [@Algebra.{contextUniverse1, contextUniverse2} K R (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance6))
  (@Ring.toSemiring.{contextUniverse2} R contextInstance7)]
    [Fintype.{contextUniverse3} I]
    [Fintype.{contextUniverse4} T]
    [Fintype.{contextUniverse5} W]
    [Fintype.{contextUniverse6} N] (f : R) (P : I → R) (hP : ∀ i, f*P i=P i) (β : I → T → K) (J : I → Matrix W N R) :
    ∀ a b, f*Csharp P β J a b=Csharp P β J a b := by
  intro a b
  simp only [Csharp,Matrix.mul_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [← mul_assoc]
  congr 1
  simp only [rep,C₀]
  split_ifs <;> simp only [Algebra.mul_smul_comm, hP, mul_zero]
lemma Dsharp_sector
    {K : Type contextUniverse1}
    {R : Type contextUniverse2}
    {I : Type contextUniverse3}
    {T : Type contextUniverse4}
    {W : Type contextUniverse5}
    {N : Type contextUniverse6}
    [contextInstance6 : Field.{contextUniverse1} K]
    [contextInstance7 : Ring.{contextUniverse2} R]
    [@Algebra.{contextUniverse1, contextUniverse2} K R (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance6))
  (@Ring.toSemiring.{contextUniverse2} R contextInstance7)]
    [Fintype.{contextUniverse3} I]
    [Fintype.{contextUniverse4} T]
    [Fintype.{contextUniverse5} W]
    [Fintype.{contextUniverse6} N] (f : R) (P : I → R) (α β : I → T → K) (Y : I → Matrix N W R)
    (hY : ∀ i n w, f*Y i n w=Y i n w) : ∀ a b, f*Dsharp P α β Y a b=Dsharp P α β Y a b := by
  intro a b
  simp only [Dsharp,Matrix.mul_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [← mul_assoc]
  congr 1
  simp only [blockY]
  split_ifs <;> simp only [hY, mul_zero]
end
end OddKaplansky.Compression

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.SquareCertificate
noncomputable section
open scoped Classical BigOperators Matrix
variable {S : Type portUniverse1} {R : Type portUniverse2} {N : Type portUniverse3} [Ring S] [Fintype R] [sectionInstance75 : Fintype N]
def cutD (σ : R → N) (D : Matrix N R S) : Matrix R R S := fun i j => D (σ i) j
def cutC (σ : R → N) (C : Matrix R N S) : Matrix R R S := fun i j => C i (σ j)
def A (f : S) (σ : R → N) (D : Matrix N R S) : Matrix R R S := cutD σ D + Matrix.diagonal (fun _ => 1-f)
def B (f : S) (σ : R → N) (C : Matrix R N S) : Matrix R R S := cutC σ C + Matrix.diagonal (fun _ => 1-f)
lemma sector_right (f x : S) (hc : Commute f x) (hx : f*x=x) : x*f=x := hc.eq.symm.trans hx
lemma complement_left (f x : S) (hx : f*x=x) : (1-f)*x=0 := by rw [sub_mul,one_mul,hx,sub_self]
lemma complement_right (f x : S) (hx : x*f=x) : x*(1-f)=0 := by rw [mul_sub,mul_one,hx,sub_self]
lemma products
    {S : Type contextUniverse1}
    {R : Type contextUniverse2}
    {N : Type contextUniverse3}
    [Ring.{contextUniverse1} S]
    [Fintype.{contextUniverse2} R]
    [Fintype.{contextUniverse3} N] (f : S) (hf : f*f=f) (hc : ∀ x, Commute f x)
    (σ : R → N) (hσ : Function.Injective σ) (C : Matrix R N S) (D : Matrix N R S)
    (hC : ∀ i j, f*C i j=C i j) (hD : ∀ i j, f*D i j=D i j)
    (hDC : D*C=Matrix.diagonal (fun _ => f)) : A f σ D * B f σ C=1 := by
  have hDC' : cutD σ D*cutC σ C=Matrix.diagonal (fun _ => f) := by
    funext i j
    change (D*C) (σ i) (σ j)=_
    rw [hDC]
    simp only [Matrix.diagonal_apply, hσ.eq_iff]
  have hleft : Matrix.diagonal (fun _ : R => 1-f)*cutC σ C=0 := by
    funext i j
    rw [Matrix.diagonal_mul]
    exact complement_left f _ (hC i (σ j))
  have hright : cutD σ D*Matrix.diagonal (fun _ : R => 1-f)=0 := by
    funext i j
    rw [Matrix.mul_diagonal]
    exact complement_right f _ (sector_right f _ (hc _) (hD (σ i) j))
  have hcomp : Matrix.diagonal (fun _ : R => 1-f)*Matrix.diagonal (fun _ : R => 1-f)=Matrix.diagonal (fun _ : R => 1-f) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    noncomm_ring [hf]
  rw [A,B,add_mul,mul_add,mul_add,hDC',hleft,hright,hcomp]
  funext i j
  by_cases he : i=j <;> simp only [add_zero, zero_add, he, Matrix.add_apply, Matrix.diagonal_apply_eq, add_sub_cancel, Matrix.one_apply, ↓reduceIte, ne_eq, not_false_eq_true, Matrix.diagonal_apply_ne, Matrix.one_apply_ne]

def u (f : S) (a : N) : N → S := Pi.single a f
def v (f : S) (C : Matrix R N S) (a : N) : R → S := C *ᵥ u f a
lemma certificate (f : S) (hf : f*f=f) (hf0 : f ≠ 0) (_hc : ∀ x, Commute f x)
    (σ : R → N) (C : Matrix R N S) (D : Matrix N R S)
    (hC : ∀ i j, f*C i j=C i j)
    (hDC : D*C=Matrix.diagonal (fun _ => f)) (a : N) (ha : ∀ i, σ i ≠ a) :
    v f C a ≠ 0 ∧ D *ᵥ v f C a=u f a ∧ A f σ D *ᵥ v f C a=0 ∧ (B f σ C*A f σ D-1)*ᵥ v f C a = -v f C a := by
  have hDu : D *ᵥ v f C a=u f a := by
    rw [v,Matrix.mulVec_mulVec,hDC]
    funext i
    simp only [Matrix.mulVec_diagonal,u]
    by_cases hi : i=a
    · subst i; simp only [Pi.single_eq_same, hf]
    · simp only [ne_eq, hi, not_false_eq_true, Pi.single_eq_of_ne, mul_zero]
  have hu : u f a ≠ 0 := by
    intro he
    have hh := congrFun he a
    exact hf0 (by simpa only [u, Pi.single_eq_same, Pi.zero_apply] using hh)
  have hv : v f C a ≠ 0 := by
    intro he
    rw [he,Matrix.mulVec_zero] at hDu
    exact hu hDu.symm
  have hvs (i : R) : f*v f C a i=v f C a i := by
    simp only [v,Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_assoc,hC]
  have hAv : A f σ D *ᵥ v f C a=0 := by
    rw [A,Matrix.add_mulVec]
    have hcut : cutD σ D *ᵥ v f C a=0 := by
      funext i
      change (D *ᵥ v f C a) (σ i)=0
      rw [hDu]
      simp only [u, ne_eq, ha i, not_false_eq_true, Pi.single_eq_of_ne]
    rw [hcut,zero_add]
    funext i
    rw [Matrix.mulVec_diagonal]
    exact complement_left f _ (hvs i)
  refine ⟨hv,hDu,hAv,?_⟩
  rw [Matrix.sub_mulVec,← Matrix.mulVec_mulVec,hAv,Matrix.mulVec_zero,Matrix.one_mulVec,zero_sub]
lemma reverse_ne (f : S) (hf : f*f=f) (hf0 : f ≠ 0) (hc : ∀ x, Commute f x)
    (σ : R → N) (C : Matrix R N S) (D : Matrix N R S)
    (hC : ∀ i j, f*C i j=C i j)
    (hDC : D*C=Matrix.diagonal (fun _ => f)) (a : N) (ha : ∀ i, σ i ≠ a) : B f σ C*A f σ D ≠ 1 := by
  obtain ⟨hv,_,hAv,_⟩ := certificate f hf hf0 hc σ C D hC hDC a ha
  intro he
  have hh := congrArg (fun E => E *ᵥ v f C a) he
  rw [← Matrix.mulVec_mulVec,hAv,Matrix.mulVec_zero,Matrix.one_mulVec] at hh
  exact hv hh.symm
end
end OddKaplansky.SquareCertificate

end

end OAI
end

section
namespace OAI

section
namespace OddKaplansky.Heisenberg
noncomputable section
open scoped Classical BigOperators
variable (M q : ℕ)
abbrev Z := Fin q → Fourier.C M
def dot (y x : Z M q) : Fourier.C M := Multiplicative.ofAdd (∑ j, (y j).toAdd * (x j).toAdd)
lemma dot_one_left (x : Z M q) : dot M q 1 x=1 := by simp only [dot, Pi.one_apply, toAdd_one, zero_mul, Finset.sum_const_zero, ofAdd_zero]
lemma dot_one_right (y : Z M q) : dot M q y 1=1 := by simp only [dot, Pi.one_apply, toAdd_one, mul_zero, Finset.sum_const_zero, ofAdd_zero]
lemma dot_mul_left (y t x : Z M q) : dot M q (y*t) x = dot M q y x * dot M q t x := by
  apply Multiplicative.toAdd.injective
  simp only [dot, Pi.mul_apply, toAdd_mul, add_mul, Finset.sum_add_distrib, ofAdd_add, ofAdd_sum, toAdd_prod, toAdd_ofAdd]
lemma dot_mul_right (y x s : Z M q) : dot M q y (x*s) = dot M q y x * dot M q y s := by
  apply Multiplicative.toAdd.injective
  simp only [dot, Pi.mul_apply, toAdd_mul, mul_add, Finset.sum_add_distrib, ofAdd_add, ofAdd_sum, toAdd_prod, toAdd_ofAdd]
lemma dot_inv_left (y x : Z M q) : dot M q y⁻¹ x = (dot M q y x)⁻¹ := by
  apply Multiplicative.toAdd.injective
  simp only [dot, Pi.inv_apply, toAdd_inv, neg_mul, Finset.sum_neg_distrib, ofAdd_neg, ofAdd_sum, toAdd_prod, toAdd_ofAdd]
lemma dot_symm (y x : Z M q) : dot M q y x=dot M q x y := by simp only [dot, ofAdd_sum, mul_comm]
structure GroupData where
  x : Z M q
  y : Z M q
  k : Fourier.C M
@[ext] lemma GroupData.ext {a b : GroupData M q} (hx : a.x=b.x) (hy : a.y=b.y) (hk : a.k=b.k) : a=b := by
  cases a; cases b; simp_all
instance : One (GroupData M q) := ⟨⟨1,1,1⟩⟩
instance : Mul (GroupData M q) := ⟨fun a b => ⟨a.x*b.x,a.y*b.y,a.k*b.k*dot M q a.y b.x⟩⟩
instance : Inv (GroupData M q) := ⟨fun a => ⟨a.x⁻¹,a.y⁻¹,a.k⁻¹*dot M q a.y a.x⟩⟩
@[simp] lemma one_x : (1 : GroupData M q).x=1 := rfl
@[simp] lemma one_y : (1 : GroupData M q).y=1 := rfl
@[simp] lemma one_k : (1 : GroupData M q).k=1 := rfl
@[simp] lemma mul_x (a b : GroupData M q) : (a*b).x=a.x*b.x := rfl
@[simp] lemma mul_y (a b : GroupData M q) : (a*b).y=a.y*b.y := rfl
@[simp] lemma mul_k (a b : GroupData M q) : (a*b).k=a.k*b.k*dot M q a.y b.x := rfl
@[simp] lemma inv_x (a : GroupData M q) : a⁻¹.x=a.x⁻¹ := rfl
@[simp] lemma inv_y (a : GroupData M q) : a⁻¹.y=a.y⁻¹ := rfl
@[simp] lemma inv_k (a : GroupData M q) : a⁻¹.k=a.k⁻¹*dot M q a.y a.x := rfl
instance : Group (GroupData M q) where
  mul_assoc a b c := by ext <;> simp only [mul_x,mul_y,mul_k,dot_mul_left,dot_mul_right,mul_assoc]; ac_rfl
  one_mul a := by ext <;> simp only [mul_x, one_x, Pi.mul_apply, Pi.one_apply, one_mul, mul_y, one_y, mul_k, one_k, dot_one_left, mul_one]
  mul_one a := by ext <;> simp only [mul_x, one_x, Pi.mul_apply, Pi.one_apply, mul_one, mul_y, one_y, mul_k, one_k, dot_one_right]
  inv_mul_cancel a := by ext <;> simp only [mul_x, inv_x, Pi.mul_apply, Pi.inv_apply, mul_comm, mul_inv_cancel, toAdd_one, one_x, Pi.one_apply, mul_y, inv_y, one_y, mul_k, inv_k, mul_inv_cancel_left, dot_inv_left, one_k]
def coordinates : GroupData M q ≃ Z M q × Z M q × Fourier.C M where
  toFun a := (a.x,a.y,a.k)
  invFun a := ⟨a.1,a.2.1,a.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance [NeZero M] : Fintype (GroupData M q) := Fintype.ofEquiv _ (coordinates M q).symm
def central : Fourier.C M →* GroupData M q where
  toFun k := ⟨1,1,k⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp only [Pi.one_apply, toAdd_one, mul_x, Pi.mul_apply, mul_one, mul_y, toAdd_mul, mul_k, dot_one_left]
def X : Z M q →* GroupData M q where
  toFun x := ⟨x,1,1⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp only [Pi.mul_apply, toAdd_mul, mul_x, Pi.one_apply, toAdd_one, mul_y, mul_one, mul_k, dot_one_left]
def Y : Z M q →* GroupData M q where
  toFun y := ⟨1,y,1⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp only [Pi.one_apply, toAdd_one, mul_x, Pi.mul_apply, mul_one, toAdd_mul, mul_y, mul_k, dot_one_right]
lemma central_injective : Function.Injective (central M q) := fun _ _ he => congrArg GroupData.k he
lemma central_commute (c : Fourier.C M) (g : GroupData M q) : Commute (central M q c) g := by
  change central M q c*g=g*central M q c
  ext <;> simp only [central, MonoidHom.coe_mk, OneHom.coe_mk, mul_x, Pi.mul_apply, Pi.one_apply, one_mul, mul_comm, mul_y, mul_k, dot_one_left, mul_one, toAdd_mul, dot_one_right]
end
end OddKaplansky.Heisenberg

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.Heisenberg
noncomputable section
open scoped Classical BigOperators Matrix
variable (M q : ℕ) [NeZero M] {K : Type portUniverse1} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
lemma character_dot (s y : Z M q) : Fourier.character M hζ s y = Fourier.cyclicCharacter M hζ (dot M q y s) := by
  rw [dot_symm]; rfl

def ρGroup : GroupData M q →* Matrix (Z M q) (Z M q) K where
  toFun g := Matrix.of fun u s => if u=s*g.x then (Fourier.cyclicCharacter M hζ g.k : K)*(Fourier.character M hζ s g.y : K) else 0
  map_one' := by ext u s; simp only [one_x, mul_one, one_k, map_one, Units.val_one, one_y, Matrix.of_apply, Matrix.one_apply]
  map_mul' g h := by
    ext u s
    rw [Matrix.mul_apply,Finset.sum_eq_single (s*h.x)]
    · simp only [Matrix.of_apply,mul_x,mul_y,mul_k,map_mul,Units.val_mul]
      by_cases he : u=s*h.x*g.x
      · rw [show s*(g.x*h.x)=s*h.x*g.x by ac_rfl,if_pos he,if_pos he,ite_true]
        rw [Fourier.character_mul,MonoidHom.mul_apply,Units.val_mul]
        simp only [character_dot]
        ring
      · simp only [show s*(g.x*h.x)=s*h.x*g.x by ac_rfl,if_neg he,zero_mul]
    · intro b _ hb
      simp only [Matrix.of_apply,if_neg hb,mul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, Matrix.of_apply, ↓reduceIte, ite_mul, zero_mul, ite_eq_right_iff, mul_eq_zero, Units.ne_zero, or_self, imp_false, IsEmpty.forall_iff]

def ρ : MonoidAlgebra K (GroupData M q) →ₐ[K] Matrix (Z M q) (Z M q) K := MonoidAlgebra.lift K _ _ (ρGroup M q hζ)
lemma ρ_single (g : GroupData M q) (c : K) (u s : Z M q) :
    ρ M q hζ (MonoidAlgebra.single g c) u s =
      if u=s*g.x then c*(Fourier.cyclicCharacter M hζ g.k : K)*(Fourier.character M hζ s g.y : K) else 0 := by
  rw [ρ,MonoidAlgebra.lift_single]
  change c*(if u=s*g.x then _ else 0)=_
  split_ifs <;> simp only [mul_assoc, mul_zero]
def f : MonoidAlgebra K (GroupData M q) := CharacterIdempotents.pushed (central M q) (Fourier.cyclicCharacter M hζ)
lemma f_idempotent (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) : f M q hζ*f M q hζ=f M q hζ := CharacterIdempotents.pushed_idempotent _ _ hc
lemma f_central (a : MonoidAlgebra K (GroupData M q)) : Commute (f M q hζ) a := CharacterIdempotents.pushed_central _ _ (central_commute M q) a
lemma ρ_f (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) : ρ M q hζ (f M q hζ)=1 := by
  ext u s
  rw [f,CharacterIdempotents.pushed_eq_sum,map_smul,map_sum]
  simp only [Matrix.smul_apply,Matrix.sum_apply,ρ_single,central,MonoidHom.coe_mk,OneHom.coe_mk,mul_one,map_one,Units.val_one,mul_one,Matrix.one_apply]
  by_cases he : u=s
  · subst u
    simp only [ite_true,inv_mul_cancel₀ (Units.ne_zero _),Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,smul_eq_mul]
    exact inv_mul_cancel₀ hc
  · simp only [Fintype.card_multiplicative, ZMod.card, he, ↓reduceIte, Finset.sum_const_zero, smul_eq_mul, mul_zero]
def p (v : Z M q) : MonoidAlgebra K (GroupData M q) := CharacterIdempotents.pushed (Y M q) (Fourier.character M hζ v)
def D (v : Z M q) : MonoidAlgebra K (GroupData M q) := f M q hζ * p M q hζ v
lemma ρ_p (hc : (Fintype.card (Z M q) : K) ≠ 0) (v : Z M q) :
    ρ M q hζ (p M q hζ v) = Matrix.single v v 1 := by
  ext u s
  rw [p,CharacterIdempotents.pushed_eq_sum,map_smul,map_sum]
  simp only [Matrix.smul_apply,Matrix.sum_apply,ρ_single,Y,MonoidHom.coe_mk,OneHom.coe_mk,mul_one,map_one,Units.val_one]
  by_cases he : u=s
  · subst u
    simp only [ite_true,smul_eq_mul]
    have hs : ∑ a : Z M q, (Fourier.character M hζ v a : K)⁻¹ * (Fourier.character M hζ s a : K) = if s=v then (Fintype.card (Z M q) : K) else 0 := by
      by_cases hsv : s=v
      · subst s; simp only [ne_eq, Units.ne_zero, not_false_eq_true, inv_mul_cancel₀, Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_multiplicative, ZMod.card, Finset.prod_const, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, mul_one, ↓reduceIte]
      · rw [if_neg hsv]
        have hh := CharacterIdempotents.sum_character_eq_zero ((Fourier.character M hζ s)*(Fourier.character M hζ v)⁻¹) (by
          intro h
          apply hsv
          apply Fourier.character_injective M hζ
          apply MonoidHom.ext
          intro a
          exact mul_inv_eq_one.mp (congrArg (fun f : Z M q →* Kˣ => f a) h))
        simpa only [mul_comm, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val] using hh
    rw [hs]
    by_cases hsv : s=v
    · subst s
      simpa only [Matrix.single_apply,ite_true,and_self] using inv_mul_cancel₀ hc
    · simp only [Fintype.card_pi, Fintype.card_multiplicative, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow, hsv, ↓reduceIte, mul_zero, Matrix.single, Matrix.of_apply, Ne.symm hsv, and_self]
  · simp only [Fintype.card_pi, Fintype.card_multiplicative, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow, he, ↓reduceIte, Finset.sum_const_zero, smul_eq_mul, mul_zero, Matrix.single, Matrix.of_apply, right_eq_ite_iff, zero_ne_one, imp_false, not_and]; rintro rfl rfl; exact he rfl
lemma ρ_D (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) (hz : (Fintype.card (Z M q) : K) ≠ 0) (v : Z M q) :
    ρ M q hζ (D M q hζ v)=Matrix.single v v 1 := by rw [D,map_mul,ρ_f M q hζ hc,one_mul,ρ_p M q hζ hz]
def xElt (u : Z M q) : MonoidAlgebra K (GroupData M q) := MonoidAlgebra.single (X M q u) 1
def Ω (u v : Z M q) : MonoidAlgebra K (GroupData M q) := xElt M q (u*v⁻¹) * D M q hζ v
lemma ρ_Ω (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) (hz : (Fintype.card (Z M q) : K) ≠ 0) (u v : Z M q) :
    ρ M q hζ (Ω M q hζ u v)=Matrix.single u v 1 := by
  rw [Ω,map_mul,ρ_D M q hζ hc hz]
  ext a b
  simp only [Matrix.mul_apply,xElt,ρ_single,X,MonoidHom.coe_mk,OneHom.coe_mk,map_one,Units.val_one,mul_one,Matrix.single]
  by_cases hb : b=v
  · subst b
    simp only [Matrix.of_apply,ite_and,mul_ite,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    simp only [mul_inv_cancel_comm_assoc, eq_comm, mul_one]
  · simp only [Matrix.of_apply, Ne.symm hb, and_false, ↓reduceIte, mul_zero, Finset.sum_const_zero]
end
end OddKaplansky.Heisenberg

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.Heisenberg
noncomputable section
open scoped Classical BigOperators Matrix
variable (M q : ℕ) [NeZero M] {K : Type portUniverse1} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) (hz : (Fintype.card (Z M q) : K) ≠ 0)
abbrev Sector := LinearMap.range (Algebra.lmul K (MonoidAlgebra K (GroupData M q)) (f M q hζ))
lemma mem_sector_of_fixed {a : MonoidAlgebra K (GroupData M q)} (ha : f M q hζ*a=a) : a ∈ Sector M q hζ := ⟨a,ha⟩
include hc in
lemma Ω_fixed (u v : Z M q) : f M q hζ*Ω M q hζ u v=Ω M q hζ u v := by
  unfold Ω D
  rw [← mul_assoc,(f_central M q hζ _).eq,mul_assoc,← mul_assoc (f M q hζ),f_idempotent M q hζ hc]
def frame (xy : Z M q × Z M q) : MonoidAlgebra K (GroupData M q) := f M q hζ * MonoidAlgebra.single ⟨xy.1,xy.2,1⟩ 1
lemma f_single (g : GroupData M q) : f M q hζ*MonoidAlgebra.single g 1 = (Fourier.cyclicCharacter M hζ g.k : K) • frame M q hζ (g.x,g.y) := by
  have hg : central M q g.k * (⟨g.x,g.y,1⟩ : GroupData M q)=g := by ext <;> simp only [central, MonoidHom.coe_mk, OneHom.coe_mk, mul_x, Pi.mul_apply, Pi.one_apply, one_mul, mul_y, mul_k, mul_one, dot_one_left]
  have hs : MonoidAlgebra.single g (1 : K)=MonoidAlgebra.single (central M q g.k) 1*MonoidAlgebra.single (⟨g.x,g.y,1⟩ : GroupData M q) 1 := by rw [MonoidAlgebra.single_mul_single,one_mul,hg]
  rw [hs,← mul_assoc]
  have hh := CharacterIdempotents.pushed_mul_single (central M q) (Fourier.cyclicCharacter M hζ) g.k
  change f M q hζ*MonoidAlgebra.single (central M q g.k) 1=(Fourier.cyclicCharacter M hζ g.k : K) • f M q hζ at hh
  rw [hh,smul_mul_assoc]
  rfl
lemma span_frame : Submodule.span K (Set.range (frame M q hζ))=Sector M q hζ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨xy,rfl⟩
    exact ⟨_,rfl⟩
  · rintro _ ⟨a,rfl⟩
    change f M q hζ*a ∈ _
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      rw [MonoidAlgebra.of_apply,f_single]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(g.x,g.y),rfl⟩)
    | add a b ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
    | smul c a ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha
lemma sector_dim_le : Module.finrank K (Sector M q hζ) ≤ Fintype.card (Z M q)*Fintype.card (Z M q) := by
  rw [← span_frame]
  simpa only [Set.finrank,Fintype.card_prod] using finrank_range_le_card (R := K) (frame M q hζ)

def encode : Matrix (Z M q) (Z M q) K →ₗ[K] MonoidAlgebra K (GroupData M q) where
  toFun T := ∑ u,∑ v,T u v • Ω M q hζ u v
  map_add' T S := by simp only [Matrix.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c T := by simp only [Matrix.smul_apply,smul_smul,smul_eq_mul,Finset.smul_sum,RingHom.id_apply]
lemma encode_apply (T : Matrix (Z M q) (Z M q) K) : encode M q hζ T=∑ u,∑ v,T u v • Ω M q hζ u v := rfl
include hc in
lemma encode_fixed (T : Matrix (Z M q) (Z M q) K) : f M q hζ*encode M q hζ T = encode M q hζ T := by
  simp only [encode_apply,Finset.mul_sum,mul_smul_comm,Ω_fixed M q hζ hc]
include hc hz in
lemma ρ_encode (T : Matrix (Z M q) (Z M q) K) : ρ M q hζ (encode M q hζ T)=T := by
  simp only [encode_apply,map_sum,map_smul,ρ_Ω M q hζ hc hz]
  ext u v
  simp only [Matrix.smul_single, smul_eq_mul, mul_one, Matrix.sum_apply, Matrix.single_apply, ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero]
include hc hz in
lemma encode_injective : Function.Injective (encode M q hζ) := by
  intro T S he
  have hh := congrArg (ρ M q hζ) he
  simpa only [ρ_encode M q hζ hc hz] using hh
include hc hz in
lemma encode_range : LinearMap.range (encode M q hζ)=Sector M q hζ := by
  apply Submodule.eq_of_le_of_finrank_le
  · rintro _ ⟨T,rfl⟩
    exact mem_sector_of_fixed _ _ _ (encode_fixed M q hζ hc T)
  · rw [LinearMap.finrank_range_of_inj (encode_injective M q hζ hc hz)]
    simpa only [Module.finrank_matrix,Module.finrank_self,mul_one] using sector_dim_le M q hζ
include hc hz in
lemma ρ_injective_on_sector {a b : MonoidAlgebra K (GroupData M q)}
    (ha : a ∈ Sector M q hζ) (hb : b ∈ Sector M q hζ) (he : ρ M q hζ a=ρ M q hζ b) : a=b := by
  rw [← encode_range M q hζ hc hz] at ha hb
  obtain ⟨T,rfl⟩ := ha
  obtain ⟨S,rfl⟩ := hb
  rw [ρ_encode M q hζ hc hz,ρ_encode M q hζ hc hz] at he
  rw [he]
include hc hz in
lemma Ω_mul (u v s t : Z M q) : Ω M q hζ u v*Ω M q hζ s t=if v=s then Ω M q hζ u t else 0 := by
  apply ρ_injective_on_sector M q hζ hc hz
  · apply mem_sector_of_fixed
    rw [← mul_assoc,Ω_fixed M q hζ hc]
  · split_ifs
    · exact mem_sector_of_fixed _ _ _ (Ω_fixed M q hζ hc _ _)
    · exact Submodule.zero_mem _
  · rw [map_mul,ρ_Ω M q hζ hc hz,ρ_Ω M q hζ hc hz]
    split_ifs with hv <;> simp only [ρ_Ω M q hζ hc hz,map_zero]
    all_goals
      ext a b
      simp only [hv, Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ite_self, Matrix.zero_apply] <;> split_ifs <;> rfl
include hc hz in
lemma Ω_ne_zero (u v : Z M q) : Ω M q hζ u v≠0 := by
  intro he
  have hh := congrArg (fun a => ρ M q hζ a u v) he
  rw [ρ_Ω M q hζ hc hz,map_zero] at hh
  simp only [Matrix.single_apply_same, Matrix.zero_apply, one_ne_zero] at hh
end
end OddKaplansky.Heisenberg

end

end OAI
end

section
namespace OAI


section

noncomputable section
open scoped Classical BigOperators
namespace OddKaplansky.MatrixBlock
variable {S : Type portUniverse1} {R : Type portUniverse2} {m : Type portUniverse3} [Ring S] [Ring R] [Fintype m]
variable (f : S →+* R) (q : m → m → R)

def block (X : Matrix m m S) : R := ∑ i, ∑ j, f (X i j) * q i j

lemma block_sub (X Y : Matrix m m S) : block f q (X - Y) = block f q X - block f q Y := by
  simp only [block, Matrix.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

variable (hqq : ∀ i j k r, q i j * q k r = if j = k then q i r else 0)
variable (hcomm : ∀ x i j, Commute (f x) (q i j))
include hqq hcomm

lemma block_mul (X Y : Matrix m m S) : block f q (X * Y) = block f q X * block f q Y := by
  have hterm (i j k r : m) :
      (f (X i j) * q i j) * (f (Y k r) * q k r) =
        if j = k then f (X i j * Y k r) * q i r else 0 := by
    calc
      _ = f (X i j * Y k r) * (q i j * q k r) := by
        rw [map_mul, ← mul_assoc, mul_assoc (f (X i j)),
          (hcomm (Y k r) i j).eq.symm]
        simp only [mul_assoc]
      _ = _ := by rw [hqq]; split_ifs <;> simp only [map_mul, mul_zero]
  have hmulij (i j : m) : (f (X i j) * q i j) * block f q Y =
      ∑ r, f (X i j * Y j r) * q i r := by
    simp only [block, Finset.mul_sum, hterm]
    rw [Finset.sum_comm]
    simp only [map_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  symm
  calc
    block f q X * block f q Y = ∑ i, ∑ j, (f (X i j) * q i j) * block f q Y := by
      change (∑ i, ∑ j, f (X i j) * q i j) * block f q Y = _
      simp only [Finset.sum_mul]
    _ = ∑ i, ∑ j, ∑ r, f (X i j * Y j r) * q i r := by simp_rw [hmulij]
    _ = block f q (X * Y) := by
      simp only [block, Matrix.mul_apply, map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm

lemma block_sandwich (X : Matrix m m S) (i j : m) :
    q i i * block f q X * q j j = f (X i j) * q i j := by
  have hterm (k r : m) : q i i * (f (X k r) * q k r) * q j j =
      if i = k then if r = j then f (X k r) * q i j else 0 else 0 := by
    calc
      _ = f (X k r) * (q i i * q k r * q j j) := by
        rw [← mul_assoc, (hcomm (X k r) i i).eq.symm]
        simp only [mul_assoc]
      _ = _ := by
        by_cases hik : i = k <;> by_cases hrj : r = j <;>
          simp only [hrj, hik, hqq, ↓reduceIte, mul_zero, zero_mul]

  simp only [block, Finset.mul_sum, Finset.sum_mul, hterm]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero, Finset.sum_ite_eq]

lemma block_injective (hpure : ∀ x i j, f x * q i j = 0 → x = 0) :
    Function.Injective (block f q) := by
  intro X Y h
  have hz : block f q (X - Y) = 0 := by rw [block_sub, h, sub_self]
  have hXY : X - Y = 0 := by
    ext i j
    apply hpure _ i j
    rw [← block_sandwich f q hqq hcomm, hz, mul_zero, zero_mul]
  exact sub_eq_zero.mp hXY

end OddKaplansky.MatrixBlock
namespace OddKaplansky.ProductAlgebras
variable {K : Type portUniverse4} {G : Type portUniverse5} {H : Type portUniverse6} [Field K] [Group G] [Group H]

def leftMap : MonoidAlgebra K G →ₐ[K] MonoidAlgebra K (G × H) :=
  MonoidAlgebra.mapDomainAlgHom K K (MonoidHom.inl G H)
def rightMap : MonoidAlgebra K H →ₐ[K] MonoidAlgebra K (G × H) :=
  MonoidAlgebra.mapDomainAlgHom K K (MonoidHom.inr G H)

lemma left_right_commute (x : MonoidAlgebra K G) (y : MonoidAlgebra K H) :
    Commute (leftMap x) (rightMap y) := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    induction y using MonoidAlgebra.induction_on with
    | of h =>
      change _ * _ = _ * _
      simp only [leftMap, MonoidAlgebra.of_apply, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single, MonoidHom.inl_apply, rightMap, MonoidHom.inr_apply, MonoidAlgebra.single_mul_single, Prod.mk_mul_mk, mul_one, one_mul]
    | add y z hy hz => simpa only [map_add] using hy.add_right hz
    | smul c y hy => simpa only [map_smul] using hy.smul_right c
  | add x z hx hz => simpa only [map_add] using hx.add_left hz
  | smul c x hx => simpa only [map_smul] using hx.smul_left c

lemma product_coeff (x : MonoidAlgebra K G) (y : MonoidAlgebra K H) (g : G) (h : H) :
    (leftMap x * rightMap y).coeff (g,h) = x.coeff g * y.coeff h := by
  induction x using MonoidAlgebra.induction_on with
  | of a =>
    induction y using MonoidAlgebra.induction_on with
    | of b =>
      by_cases hag : a = g <;> by_cases hbh : b = h <;>
        simp only [leftMap, hag, MonoidAlgebra.of_apply, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single, MonoidHom.inl_apply, rightMap, hbh, MonoidHom.inr_apply, MonoidAlgebra.single_mul_single, Prod.mk_mul_mk, mul_one, one_mul, MonoidAlgebra.coeff_single, Finsupp.single_eq_same, ne_eq, Prod.ext_iff, and_false, not_false_eq_true, Finsupp.single_eq_of_ne', mul_zero, and_true, and_self]
    | add y z hy hz =>
      simp only [map_add, mul_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, hy, hz]
    | smul c y hy =>
      simp only [map_smul, mul_smul_comm, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
        smul_eq_mul, hy]
      ring
  | add x z hx hz =>
    simp only [map_add, add_mul, MonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hz]
  | smul c x hx =>
    simp only [map_smul, smul_mul_assoc, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
      smul_eq_mul, hx]
    ring

lemma product_ne_zero {x : MonoidAlgebra K G} {y : MonoidAlgebra K H}
    (hx : x ≠ 0) (hy : y ≠ 0) : leftMap x * rightMap y ≠ 0 := by
  obtain ⟨g,hg⟩ : ∃ g, x.coeff g ≠ 0 := by
    by_contra! h
    apply hx
    ext g
    exact h g
  obtain ⟨h,hh⟩ : ∃ h, y.coeff h ≠ 0 := by
    by_contra! h
    apply hy
    ext a
    exact h a
  intro he
  have he' := congrArg (fun z : MonoidAlgebra K (G × H) => z.coeff (g,h)) he
  rw [product_coeff] at he'
  exact mul_ne_zero hg hh he'

end OddKaplansky.ProductAlgebras
namespace OddKaplansky.MatrixBlock
variable {S : Type portUniverse7} {R : Type portUniverse8} {m : Type portUniverse9} [Ring S] [Ring R] [Fintype m]
variable (f : S →+* R) (q : m → m → R)

def output (X : Matrix m m S) : R := 1 - block f q 1 + block f q X

variable (hqq : ∀ i j k r, q i j * q k r = if j = k then q i r else 0)
variable (hcomm : ∀ x i j, Commute (f x) (q i j))

include hqq hcomm in
theorem prescribed_scalar_products
    (hpure : ∀ x i j, f x * q i j = 0 → x = 0)
    (a b : Matrix m m S) (hab : a * b = 1) (hba : b * a ≠ 1) :
    output f q a * output f q b = 1 ∧ output f q b * output f q a ≠ 1 := by
  let e := block f q 1
  let a' := 1 - e + block f q a
  let b' := 1 - e + block f q b
  have he : e * e = e := by rw [← block_mul f q hqq hcomm, mul_one]
  have hea : e * block f q a = block f q a := by rw [← block_mul f q hqq hcomm, one_mul]
  have hae : block f q a * e = block f q a := by rw [← block_mul f q hqq hcomm, mul_one]
  have heb : e * block f q b = block f q b := by rw [← block_mul f q hqq hcomm, one_mul]
  have hbe : block f q b * e = block f q b := by rw [← block_mul f q hqq hcomm, mul_one]
  have hab' : block f q a * block f q b = e := by rw [← block_mul f q hqq hcomm, hab]
  change a' * b' = 1 ∧ b' * a' ≠ 1
  refine ⟨?_,?_⟩
  · dsimp [a',b']
    noncomm_ring [he, hea, hae, heb, hbe, hab']
  · intro h
    have h' : block f q b * block f q a = e := by
      apply add_left_cancel (a := 1 - e)
      calc
        1 - e + block f q b * block f q a =
            (1 - e + block f q b) * (1 - e + block f q a) := by
          noncomm_ring [he, hea, hae, heb, hbe]
        _ = 1 := h
        _ = 1 - e + e := by abel
    apply hba
    apply block_injective f q hqq hcomm hpure
    rw [block_mul f q hqq hcomm]
    exact h'

end OddKaplansky.MatrixBlock
end

end

end OAI
end

section
namespace OAI



section
namespace OddKaplansky.Heisenberg
noncomputable section
open scoped Classical BigOperators Matrix
variable (M q : ℕ) [NeZero M] {K : Type portUniverse1} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) (hz : (Fintype.card (Z M q) : K) ≠ 0)

def scalar {L : Type portUniverse2} [Group L] (T : Matrix (Z M q) (Z M q) (MonoidAlgebra K L)) : MonoidAlgebra K (L×GroupData M q) :=
  MatrixBlock.output (ProductAlgebras.leftMap (K := K) (G := L) (H := GroupData M q)).toRingHom
    (fun u v => ProductAlgebras.rightMap (G := L) (Ω M q hζ u v)) T
include hc hz in
lemma scalar_products {L : Type portUniverse3} [Group L] (A B : Matrix (Z M q) (Z M q) (MonoidAlgebra K L))
    (hAB : A*B=1) (hBA : B*A≠1) : scalar M q hζ A*scalar M q hζ B=1 ∧ scalar M q hζ B*scalar M q hζ A≠1 := by
  apply MatrixBlock.prescribed_scalar_products
  · intro u v s t
    rw [← map_mul,Ω_mul M q hζ hc hz]
    split_ifs <;> simp only [map_zero]
  · intro x u v
    exact ProductAlgebras.left_right_commute x (Ω M q hζ u v)
  · intro x u v he
    by_contra hx
    exact ProductAlgebras.product_ne_zero hx (Ω_ne_zero M q hζ hc hz u v) he
  · convert hAB using 1 ; congr ; exact Subsingleton.elim _ _
  · convert hBA using 1 ; congr ; exact Subsingleton.elim _ _
end
end OddKaplansky.Heisenberg

namespace OddKaplansky.Padding
noncomputable section
open scoped Classical BigOperators Matrix
variable {R : Type portUniverse5} {I : Type portUniverse6} {J : Type portUniverse7} [Ring R] [sectionInstance76 : Fintype I] [sectionInstance77 : Fintype J]
def pad (T : Matrix I I R) : Matrix (I⊕J) (I⊕J) R := Matrix.fromBlocks T 0 0 1
lemma pad_mul (A B : Matrix I I R) : pad (J := J) (A*B)=pad A*pad B := by simp only [pad, Matrix.fromBlocks_multiply, Matrix.mul_zero, add_zero, Matrix.mul_one, Matrix.zero_mul, mul_one, zero_add]
lemma pad_one
    {R : Type contextUniverse1}
    {I : Type contextUniverse2}
    {J : Type contextUniverse3}
    [Ring.{contextUniverse1} R]
    [Fintype.{contextUniverse2} I]
    [Fintype.{contextUniverse3} J] : pad (R := R) (I := I) (J := J) 1=1 := Matrix.fromBlocks_one
lemma pad_ne_one
    {R : Type contextUniverse1}
    {I : Type contextUniverse2}
    {J : Type contextUniverse3}
    [Ring.{contextUniverse1} R]
    [Fintype.{contextUniverse2} I]
    [Fintype.{contextUniverse3} J] {T : Matrix I I R} (h : T≠1) : pad (J := J) T≠1 := by
  intro he
  apply h
  funext i j
  have hh := congrFun (congrFun he (Sum.inl i)) (Sum.inl j)
  simpa only [Matrix.one_apply, pad, Matrix.fromBlocks_apply₁₁, Sum.inl.injEq] using hh
lemma products (A B : Matrix I I R) (hAB : A*B=1) (hBA : B*A≠1) :
    pad (J := J) A*pad B=1 ∧ pad (J := J) B*pad A≠1 := by
  rw [← pad_mul,← pad_mul,hAB,pad_one]
  exact ⟨rfl,pad_ne_one hBA⟩
end
end OddKaplansky.Padding

namespace OddKaplansky.FixedField
noncomputable section
open scoped Classical BigOperators Matrix
variable (M : ℕ) (hM : 2≤M) (r : ℕ)
include hM in
lemma power_search : ∃ q, r≤M^q := by
  refine ⟨r,?_⟩
  exact (Nat.le_of_lt (Nat.lt_two_pow_self (n := r))).trans (Nat.pow_le_pow_left hM r)
def leastQ : ℕ := Nat.find (power_search M hM r)
lemma leastQ_spec : r≤M^(leastQ M hM r) := Nat.find_spec (power_search M hM r)
variable [NeZero M] {K : Type portUniverse8} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (M : K)≠0)
@[instance_reducible]
def coordinateOrder : LinearOrder (Heisenberg.Z M (leastQ M hM r)) :=
  @FiniteChoice.functionOrder (Fin (leastQ M hM r)) (Fourier.C M) inferInstance inferInstance (SourceOrders.cyclic M)
def indices : (Fin r⊕Fin (M^(leastQ M hM r)-r)) ≃ Heisenberg.Z M (leastQ M hM r) :=
  finSumFinEquiv.trans ((finCongr (by
    have hh := leastQ_spec M hM r
    simp only [Heisenberg.Z,Fintype.card_fun,Fintype.card_fin,Fourier.C,Fintype.card_multiplicative,ZMod.card]
    omega)).trans (@FiniteChoice.orderedIndex _ (coordinateOrder M hM r) inferInstance).symm)
def pad {L : Type portUniverse9} [Group L] (A : Matrix (Fin r) (Fin r) (MonoidAlgebra K L)) :
    Matrix (Heisenberg.Z M (leastQ M hM r)) (Heisenberg.Z M (leastQ M hM r)) (MonoidAlgebra K L) :=
  Matrix.reindexAlgEquiv K (MonoidAlgebra K L) (indices M hM r) (Padding.pad A)
def output {L : Type portUniverse10} [Group L] (A : Matrix (Fin r) (Fin r) (MonoidAlgebra K L)) :
    MonoidAlgebra K (L×Heisenberg.GroupData M (leastQ M hM r)) := Heisenberg.scalar M (leastQ M hM r) hζ (pad M hM r A)
include hc in
lemma output_products {L : Type portUniverse11} [Group L] (A B : Matrix (Fin r) (Fin r) (MonoidAlgebra K L))
    (hAB : A*B=1) (hBA : B*A≠1) : output M hM r hζ A*output M hM r hζ B=1 ∧ output M hM r hζ B*output M hM r hζ A≠1 := by
  have hcc : (Fintype.card (Fourier.C M) : K)≠0 := by simpa only [Fourier.C, Fintype.card_multiplicative, ZMod.card, ne_eq] using hc
  have hzz : (Fintype.card (Heisenberg.Z M (leastQ M hM r)) : K)≠0 := by
    simpa only [Heisenberg.Z, Fourier.C, Fintype.card_pi, Fintype.card_multiplicative, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow, ne_eq, pow_eq_zero_iff', not_and, Decidable.not_not] using pow_ne_zero (leastQ M hM r) hc
  have hpad := Padding.products (J := Fin (M^(leastQ M hM r)-r)) A B
    (by convert hAB using 1 ; congr ; exact Subsingleton.elim _ _)
    (by convert hBA using 1 ; congr ; exact Subsingleton.elim _ _)
  let E := Matrix.reindexAlgEquiv K (MonoidAlgebra K L) (indices M hM r)
  have hone : E 1=1 := map_one E
  have hmul : ∀ X Y, E (X*Y)=E X*E Y := fun X Y => map_mul E X Y
  apply Heisenberg.scalar_products M (leastQ M hM r) hζ hcc hzz
  · change E (Padding.pad A)*E (Padding.pad B)=1
    rw [← hmul]
    have hh : E (Padding.pad A*Padding.pad B)=E 1 := by apply congrArg E; convert hpad.1 using 1 ; congr ; exact Subsingleton.elim _ _
    exact hh.trans hone
  · intro he
    apply hpad.2
    have hh : E (Padding.pad B*Padding.pad A)=E 1 := by
      rw [hmul,hone]
      exact he
    convert E.injective hh using 1 ; congr ; exact Subsingleton.elim _ _

end
end OddKaplansky.FixedField

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.Cellular
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {G : Type portUniverse2} [Field K] [Group G]
def rightShift (u : G) : Module.End K (G → K) where
  toFun x g := x (g*u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def shift : G →* Module.End K (G → K) where
  toFun := rightShift
  map_one' := by ext x g; simp only [rightShift, mul_one, LinearMap.coe_mk, AddHom.coe_mk, Module.End.one_apply]
  map_mul' u v := by ext x g; simp only [rightShift, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, mul_assoc]
def operator : MonoidAlgebra K G →ₐ[K] Module.End K (G → K) := MonoidAlgebra.lift K _ _ shift
lemma operator_single (u : G) (c : K) (x : G → K) (g : G) : operator (MonoidAlgebra.single u c) x g=c*x (g*u) := by
  rw [operator,MonoidAlgebra.lift_single]
  rfl
lemma operator_formula (a : MonoidAlgebra K G) (x : G → K) (g : G) : operator a x g=∑ u ∈ a.coeff.support, a.coeff u*x (g*u) := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single a]
  simp only [Finsupp.sum,map_sum,LinearMap.sum_apply,Finset.sum_apply,operator_single]
lemma operator_mul (a b : MonoidAlgebra K G) (x : G → K) : operator (a*b) x=operator a (operator b x) := by rw [map_mul]; rfl
lemma operator_one (x : G → K) : operator (1 : MonoidAlgebra K G) x=x := by rw [map_one]; rfl
lemma indicator_eval (a : MonoidAlgebra K G) (h : G) : operator a (Pi.single h 1) 1=a.coeff h := by
  rw [operator_formula]
  simp only [one_mul,Pi.single_apply,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hh
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hh).symm

def IsCellular (F : (G → K) → (G → K)) : Prop :=
  ∃ S : Finset G, ∃ rule : (S → K) → K, ∀ x g, F x g=rule (fun u => x (g*u))
lemma operator_cellular (a : MonoidAlgebra K G) : IsCellular (operator a) := by
  refine ⟨a.coeff.support,fun z => ∑ u : a.coeff.support, a.coeff u*z u,?_⟩
  intro x g
  rw [operator_formula]
  exact (Finset.sum_attach a.coeff.support (fun u => a.coeff u*x (g*u))).symm
lemma left_inverse (a b : MonoidAlgebra K G) (hab : a*b=1) : Function.LeftInverse (operator a) (operator b) := by
  intro x
  rw [← operator_mul,hab,operator_one]
lemma range_eq (a b : MonoidAlgebra K G) (hab : a*b=1) : Set.range (operator b)={y | operator (b*a) y=y} := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    change operator (b*a) (operator b x)=operator b x
    rw [operator_mul,left_inverse a b hab x]
  · intro hy
    exact ⟨operator a y,by rw [← operator_mul]; exact hy⟩
lemma missing_indicator (a b : MonoidAlgebra K G) (hab : a*b=1) (h : G) (hh : (b*a-1).coeff h ≠ 0) :
    Pi.single h 1 ∉ Set.range (operator b) := by
  rw [range_eq a b hab]
  intro he
  have hv := congrFun he 1
  rw [indicator_eval] at hv
  apply hh
  change (b*a).coeff h-(1 : MonoidAlgebra K G).coeff h=0
  rw [← indicator_eval (1 : MonoidAlgebra K G),operator_one,hv,sub_self]
lemma theorem_all_configurations (a b : MonoidAlgebra K G) (hab : a*b=1) (hba : b*a≠1) :
    IsCellular (operator b) ∧ Function.Injective (operator b) ∧ ¬Function.Surjective (operator b) ∧
    Set.range (operator b)={y | operator (b*a) y=y} ∧
    ∃ h : G, (b*a-1).coeff h ≠ 0 ∧ Pi.single h 1 ∉ Set.range (operator b) := by
  have hex : ∃ h : G, (b*a-1).coeff h≠0 := by
    by_contra! hh
    apply hba
    apply sub_eq_zero.mp
    ext h
    exact hh h
  obtain ⟨h,hh⟩ := hex
  have hm := missing_indicator a b hab h hh
  exact ⟨operator_cellular b,(left_inverse a b hab).injective,
    fun hs => hm (hs (Pi.single h 1)),range_eq a b hab,h,hh,hm⟩
end
end OddKaplansky.Cellular

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.IndexCut
variable {S : Type portUniverse1} {L : Type portUniverse2} {r n : ℕ} (s : S ≃ Fin r) (l : L ≃ Fin n) (hn : r < n)
def inclusion (i : S) : L := l.symm (Fin.castLE hn.le (s i))
lemma injective : Function.Injective (inclusion s l hn) := by
  intro i j he
  apply s.injective
  apply Fin.ext
  have hh := congrArg (fun x => (l x).val) he
  simpa only [inclusion,Equiv.apply_symm_apply,Fin.val_castLE] using hh
def extra : L := l.symm ⟨n-1,by omega⟩
lemma misses (i : S) : inclusion s l hn i ≠ extra l hn := by
  intro he
  have hh := congrArg (fun x => (l x).val) he
  simp only [inclusion,extra,Equiv.apply_symm_apply,Fin.val_castLE] at hh
  have hi := (s i).isLt
  omega
end OddKaplansky.IndexCut

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.Construction
noncomputable section
local instance constructionDecidableEq (α : Type portUniverse1) : DecidableEq α := Classical.decEq α
open scoped Classical BigOperators Matrix
open SourceGluing SourceGraph
local notation "M" => SourceGluing.modulus
local notation "p" => SourceGluing.p
local notation "HH" => SourceGluing.H
local notation "G₀" => SourceGluing.G₀
lemma prime_large : 1200<p := sourceM_large.trans_lt p_gt
lemma p_ne_two : p≠2 := by have := prime_large; omega
lemma p_odd : Odd p := by rw [SourceGluing.p_def]; exact sourcePrime_odd
lemma minus_square : IsSquare (-1 : ZMod p) := by
  have hd : p∣(Nat.factorial sourceM)^2+1 := by rw [SourceGluing.p_def]; exact sourcePrime_dvd
  exact neg_one_isSquare_of_dvd p (Nat.factorial sourceM) hd
lemma modulus_eq : M+1=p^4 := by
  unfold SourceGluing.modulus
  have hp : 1≤p^4 := Nat.one_le_pow 4 p (by have := prime_large; omega)
  omega
def ell := (p-1)/2
lemma pell : p=2*ell+1 := by
  obtain ⟨k,hk⟩ := p_odd
  unfold ell
  omega
lemma ell_le : ell≤p-ell := by have := pell; omega

variable {K : Type} [Field K] [sectionInstance78 : Fintype K] [sectionInstance79 : CharP K p]
lemma modulus_cast
    {K : Type}
    [contextInstance1 : Field.{0} K]
    [Fintype.{0} K]
    [@CharP.{0} K
  (@AddGroupWithOne.toAddMonoidWithOne.{0} K
    (@Ring.toAddGroupWithOne.{0} K (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K contextInstance1))))
  OddKaplansky.SourceGluing.p] : (M : K) ≠ 0 := by
  have hc := congrArg (fun n : ℕ => (n : K)) modulus_eq
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_pow,CharP.cast_eq_zero K p,zero_pow (by decide : 4≠0)] at hc
  intro hz
  rw [hz,zero_add] at hc
  exact one_ne_zero hc
lemma cyclic_card : (Fintype.card (Fourier.C M) : K)≠0 := by simpa only [Fourier.C, Fintype.card_multiplicative, ZMod.card, ne_eq] using modulus_cast (K := K)
lemma sector_base_card : (Fintype.card (WreathFourier.Base (H := HH) M) : K)≠0 := by
  simp only [WreathFourier.Base,Fintype.card_fun,Fourier.C,Fintype.card_multiplicative,ZMod.card,Nat.cast_pow]
  exact pow_ne_zero _ (modulus_cast (K := K))
lemma field_units_card
    {K : Type}
    [contextInstance1 : Field.{0} K]
    [Fintype.{0} K]
    [@CharP.{0} K
  (@AddGroupWithOne.toAddMonoidWithOne.{0} K
    (@Ring.toAddGroupWithOne.{0} K (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K contextInstance1))))
  OddKaplansky.SourceGluing.p] (hK : Fintype.card K=p^4) : Fintype.card Kˣ=M := by
  rw [Fintype.card_units,hK]
  unfold SourceGluing.modulus
  rfl
lemma local_lamp : WreathFourier.base M (WreathFourier.lamp (H := ModularSource.P p) M)=LocalGroup.c p M := by
  ext x
  · by_cases hx : x=1
    · subst x; simp only [WreathFourier.base, WreathFourier.lamp, MonoidHom.coe_mk, OneHom.coe_mk, Pi.mulSingle_eq_same, toAdd_ofAdd, LocalGroup.c, toAdd_eq_zero, ↓reduceIte]
    · have hx' : x.toAdd ≠ 0 := hx
      simp only [WreathFourier.base, WreathFourier.lamp, MonoidHom.coe_mk, OneHom.coe_mk, ne_eq, hx, not_false_eq_true, Pi.mulSingle_eq_of_ne, toAdd_one, LocalGroup.c, toAdd_eq_zero, ↓reduceIte, ofAdd_zero]
  · rfl
lemma local_conjugate
    {K : Type}
    [contextInstance1 : Field.{0} K]
    [Fintype.{0} K]
    [@CharP.{0} K
  (@AddGroupWithOne.toAddMonoidWithOne.{0} K
    (@Ring.toAddGroupWithOne.{0} K (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K contextInstance1))))
  OddKaplansky.SourceGluing.p] (s : ModularSource.P p) :
    WreathFourier.baseElt (K := K) M (WreathFourier.lamp (H := ModularSource.P p) M)*WreathFourier.topElt M s*WreathFourier.baseElt M (WreathFourier.lamp (H := ModularSource.P p) M)⁻¹=
      MonoidAlgebra.single (LocalGroup.v p M s) 1 := by
  simp only [WreathFourier.baseElt,WreathFourier.topElt,MonoidAlgebra.single_mul_single,one_mul,map_inv,local_lamp]
  rfl

structure LocalDatum where
  e : MonoidAlgebra K HH
  idem : e*e=e
  leftAnn : ∀ s : ModularSource.P p, (MonoidAlgebra.single (LocalGroup.u p M s) 1-1)^ell*e=0
  rightAnn : ∀ s : ModularSource.P p, e*(MonoidAlgebra.single (LocalGroup.v p M s) 1-1)^ell=0
  rank : Fintype.card HH<96*Module.finrank K (LinearMap.range (Algebra.lmul K _ e))

def prescribedLocalDatum {ζ : K} (hζ : IsPrimitiveRoot ζ M) (hK : Fintype.card K=p^4) : LocalDatum (K := K) where
  e := ModularSource.explicitElement p M ell hζ
  idem := (ModularSource.explicit_properties p M ell hζ (by have := prime_large; omega) pell modulus_eq (field_units_card hK)).1
  leftAnn s := (ModularSource.explicit_properties p M ell hζ (by have := prime_large; omega) pell modulus_eq (field_units_card hK)).2.1 s |>.1
  rightAnn s := by
    simpa only [local_conjugate] using (ModularSource.explicit_properties p M ell hζ (by have := prime_large; omega) pell modulus_eq (field_units_card hK)).2.1 s |>.2
  rank := by
    exact (ModularSource.explicit_properties p M ell hζ (by have := prime_large; omega) pell modulus_eq (field_units_card hK)).2.2

def push (v : Vertex) : MonoidAlgebra K HH →ₐ[K] MonoidAlgebra K G₀ := MonoidAlgebra.mapDomainAlgHom K K (SourceGluing.vertex v)
lemma ordered_zero
    {K : Type}
    [contextInstance1 : Field.{0} K]
    [Fintype.{0} K]
    [@CharP.{0} K
  (@AddGroupWithOne.toAddMonoidWithOne.{0} K
    (@Ring.toAddGroupWithOne.{0} K (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K contextInstance1))))
  OddKaplansky.SourceGluing.p] (d : LocalDatum (K := K)) (v w : Vertex) (hvw : v<w) (hvwadj : graph.Adj v w) : push v d.e*push w d.e=0 := by
  let edge : SourceGraph.Edge := ⟨(v,w),hvw,hvwadj⟩
  have hleft : SourceGluing.edgeHom v edge=LocalGroup.edgeHom p M true (index w) := by
    simp only [edgeHom, decide_true, neighbor, GraphEdges.neighbor, ↓reduceIte, edge]
  have hright : SourceGluing.edgeHom w edge=LocalGroup.edgeHom p M false (index v) := by
    have hne : w≠v := ne_of_gt hvw
    simp only [edgeHom, hne, decide_false, neighbor, GraphEdges.neighbor, ↓reduceIte, edge]
  apply OrderedZero.product_zero p ell ell_le
    (SourceGluing.edgeHom v edge) (by rw [hleft]; exact LocalGroup.edgeHom_injective p M true _) (SourceGluing.edgeHom w edge)
    (SourceGluing.vertex v) (SourceGluing.vertex w)
  · exact Gluing.edge_eq SourceGraph.Inc SourceGluing.edgeHom edge v w (CyclicAlgebra.gen p) (Or.inl rfl) (Or.inr rfl)
  · rw [hleft]
    exact d.rightAnn ((LocalGroup.line p (index w)).toMultiplicative (CyclicAlgebra.gen p))
  · rw [hright]
    exact d.leftAnn ((LocalGroup.line p (index v)).toMultiplicative (CyclicAlgebra.gen p))
end
end OddKaplansky.Construction

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.Construction
noncomputable section
local instance sectorConstructionDecidableEq (α : Type portUniverse1) : DecidableEq α := Classical.decEq α
open scoped Classical BigOperators Matrix
open SourceGluing SourceGraph
local notation "M" => SourceGluing.modulus
local notation "p" => SourceGluing.p
local notation "HH" => SourceGluing.H
abbrev G₁ := SectorGroup.G₁ M SourceGluing.vertex
instance : Group.FG G₁ := inferInstance
variable {K : Type} [Field K] [sectionInstance80 : Fintype K] [sectionInstance81 : CharP K p]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ M)
abbrev R := MonoidAlgebra K G₁
def f : R (K := K) := SectorGroup.f M SourceGluing.vertex hζ
lemma f_idem : f hζ*f hζ=f hζ := SectorGroup.f_idempotent M SourceGluing.vertex hζ cyclic_card
lemma f_nonzero : f hζ≠0 := SectorGroup.f_ne_zero M SourceGluing.vertex hζ SourceGluing.vertex_injective cyclic_card
lemma f_commute
    {K : Type}
    [contextInstance1 : Field.{0} K]
    [Fintype.{0} K]
    [@CharP.{0} K
  (@AddGroupWithOne.toAddMonoidWithOne.{0} K
    (@Ring.toAddGroupWithOne.{0} K (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K contextInstance1))))
  OddKaplansky.SourceGluing.p]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{0} K (@CommRing.toCommMonoid.{0} K (@Field.toCommRing.{0} K contextInstance1)) ζ
  OddKaplansky.SourceGluing.modulus) (a : R (K := K)) : Commute (f hζ) a := SectorGroup.f_central M SourceGluing.vertex hζ a
def original : MonoidAlgebra K SourceGluing.G₀ →ₐ[K] R (K := K) := MonoidAlgebra.mapDomainAlgHom K K (SectorGroup.original M SourceGluing.vertex)
def attached (v : Vertex) : MonoidAlgebra K (WreathFourier.Wreath (H := HH) M) →ₐ[K] R (K := K) :=
  MonoidAlgebra.mapDomainAlgHom K K (SectorGroup.factor M SourceGluing.vertex v)
def P (d : LocalDatum (K := K)) (v : Vertex) : R (K := K) := f hζ*original (push v d.e)
lemma f_mul_product (x y : R (K := K)) : (f hζ*x)*(f hζ*y)=f hζ*(x*y) := by
  calc
    _ = f hζ*(x*f hζ)*y := by simp only [mul_assoc]
    _ = f hζ*(f hζ*x)*y := by rw [← (f_commute hζ x).eq]
    _ = (f hζ*f hζ)*(x*y) := by simp only [mul_assoc]
    _ = _ := by rw [f_idem]
lemma P_idem (d : LocalDatum (K := K)) (v : Vertex) : P hζ d v*P hζ d v=P hζ d v := by
  rw [P,f_mul_product,← map_mul,← map_mul,d.idem]
lemma P_sector (d : LocalDatum (K := K)) (v : Vertex) : f hζ*P hζ d v=P hζ d v := by rw [P,← mul_assoc,f_idem]
lemma P_ordered (d : LocalDatum (K := K)) (v w : Vertex) (hvw : v<w) (hadj : graph.Adj v w) : P hζ d v*P hζ d w=0 := by
  rw [P,P,f_mul_product,← map_mul,ordered_zero d v w hvw hadj,map_zero,mul_zero]
lemma fit_upper (d : LocalDatum (K := K)) (v w : Vertex) (hvw : v<w) :
    (∑ T : SourceFit.Slot, SourceFit.alpha (K := K) v T*SourceFit.beta w T) • (P hζ d v*P hζ d w)=0 := by
  by_cases ha : graph.Adj v w
  · rw [P_ordered hζ d v w hvw ha,smul_zero]
  · change SourceFit.fitting v w • _=0
    rw [SourceFit.fitting_nonedge v w (ne_of_lt hvw) ha,zero_smul]

abbrev W := Fin (Fintype.card HH)
abbrev N (d : LocalDatum (K := K)) := Fin (Module.finrank K (LinearMap.range (Algebra.lmul K _ d.e)))
structure Rectangular (d : LocalDatum (K := K)) where
  J : Vertex → Matrix W (N d) (R (K := K))
  Y : Vertex → Matrix (N d) W (R (K := K))
  YJ : ∀ v, Y v*J v=Matrix.diagonal (fun _ => f hζ)
  JY : ∀ v, J v*Y v=Matrix.diagonal (fun _ => P hζ d v)
  sectorJ : ∀ v w n, f hζ*J v w n=J v w n
  sectorY : ∀ v n w, f hζ*Y v n w=Y v n w

def prescribedRectangles (d : LocalDatum (K := K)) : Rectangular hζ d := by
  let J := OrderedSourceSector.explicitJ M p hζ d.e d.idem (W := W) (N := N d) (Fintype.card_fin _) (Fintype.card_fin _)
  let Y := OrderedSourceSector.explicitY M p hζ d.e d.idem (W := W) (N := N d) (Fintype.card_fin _) (Fintype.card_fin _)
  have hs := OrderedSourceSector.explicit_properties M p hζ d.e d.idem (W := W) (N := N d) (Fintype.card_fin _) (Fintype.card_fin _) sector_base_card cyclic_card
  obtain ⟨hYJ,hJY,hJ,hY⟩ := hs
  let Js (v : Vertex) := J.map (attached (K := K) v)
  let Ys (v : Vertex) := Y.map (attached (K := K) v)
  have hff (v : Vertex) : attached (K := K) v (SectorFourier.f M hζ)=f hζ := SectorGroup.factor_f M SourceGluing.vertex hζ v
  have hee (v : Vertex) : attached (K := K) v (MonoidAlgebra.mapDomainAlgHom K K (WreathFourier.top M) d.e)=original (push v d.e) :=
    SectorGroup.factor_original M SourceGluing.vertex v d.e
  refine ⟨Js,Ys,?_,?_,?_,?_⟩
  · intro v
    dsimp [Js,Ys]
    rw [← Matrix.map_mul,hYJ]
    funext i j
    by_cases he : i=j <;> simp only [he, Matrix.map_apply, Matrix.diagonal_apply_eq, hff, ne_eq, not_false_eq_true, Matrix.diagonal_apply_ne, map_zero]
  · intro v
    dsimp [Js,Ys]
    rw [← Matrix.map_mul,hJY]
    funext i j
    by_cases he : i=j
    · subst j
      simp only [Matrix.map_apply,Matrix.diagonal_apply_eq,map_mul,hff,hee,P]
    · simp only [MonoidAlgebra.mapDomainAlgHom_apply, Matrix.map_apply, ne_eq, he, not_false_eq_true, Matrix.diagonal_apply_ne, map_zero]
  · intro v w n
    change f hζ*attached v (J w n)=attached v (J w n)
    rw [← hff,← map_mul,hJ]
  · intro v n w
    change f hζ*attached v (Y n w)=attached v (Y n w)
    rw [← hff,← map_mul,hY]

def ix : Vertex ≃o Fin (Fintype.card Vertex) := (Fintype.orderIsoFinOfCardEq Vertex rfl).symm
abbrev Small := W×SourceFit.Slot
abbrev Large (d : LocalDatum (K := K)) := Vertex×N d
def C (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : Matrix Small (Large d) (R (K := K)) :=
  Compression.Csharp (K := K) (P hζ d) SourceFit.beta rect.J
def D (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : Matrix (Large d) Small (R (K := K)) :=
  Compression.Dsharp (K := K) (P hζ d) SourceFit.alpha SourceFit.beta rect.Y
lemma DC (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : D hζ d rect*C hζ d rect=Matrix.diagonal (fun _ => f hζ) := by
  have hdiag (v : Vertex) : ∑ t, SourceFit.alpha (K := K) v t*SourceFit.beta v t=1 := SourceFit.fitting_diagonal p prime_large v
  have hu (v w : Vertex) (hvw : (ix v).val < (ix w).val) :
      (∑ t, SourceFit.alpha (K := K) v t*SourceFit.beta w t) • (P hζ d v*P hζ d w)=0 :=
    fit_upper hζ d v w (ix.lt_iff_lt.mp hvw)
  have hyj : ∀ v, rect.Y v*rect.J v= @Matrix.diagonal (N d) (R (K := K)) (Classical.decEq _) _ (fun _ => f hζ) := by
    intro v
    convert rect.YJ v using 1 ; congr ; exact Subsingleton.elim _ _
  have hjy : ∀ v, rect.J v*rect.Y v= @Matrix.diagonal W (R (K := K)) (Classical.decEq _) _ (fun _ => P hζ d v) := by
    intro v
    convert rect.JY v using 1 ; congr ; exact Subsingleton.elim _ _
  convert Compression.compressed (K := K) (f hζ) (f_idem hζ) (P hζ d) (P_idem hζ d)
    SourceFit.alpha SourceFit.beta ix ix.injective hdiag hu rect.J rect.Y hyj hjy using 1 <;> congr ; exact Subsingleton.elim _ _
lemma DC_classical (d : LocalDatum (K := K)) (rect : Rectangular hζ d) :
    D hζ d rect*C hζ d rect= @Matrix.diagonal (Large d) (R (K := K)) (Classical.decEq _) _ (fun _ => f hζ) := by
  convert DC hζ d rect using 1 ; congr ; exact Subsingleton.elim _ _
lemma C_sector (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : ∀ a b, f hζ*C hζ d rect a b=C hζ d rect a b :=
  Compression.Csharp_sector (K := K) (f hζ) (P hζ d) (P_sector hζ d) SourceFit.beta rect.J
lemma D_sector
    {K : Type}
    [contextInstance1 : Field.{0} K]
    [Fintype.{0} K]
    [@CharP.{0} K
  (@AddGroupWithOne.toAddMonoidWithOne.{0} K
    (@Ring.toAddGroupWithOne.{0} K (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K contextInstance1))))
  OddKaplansky.SourceGluing.p]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{0} K (@CommRing.toCommMonoid.{0} K (@Field.toCommRing.{0} K contextInstance1)) ζ
  OddKaplansky.SourceGluing.modulus) (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : ∀ a b, f hζ*D hζ d rect a b=D hζ d rect a b :=
  Compression.Dsharp_sector (K := K) (f hζ) (P hζ d) SourceFit.alpha SourceFit.beta rect.Y rect.sectorY
lemma d_positive
    {K : Type}
    [contextInstance1 : Field.{0} K]
    [Fintype.{0} K]
    [@CharP.{0} K
  (@AddGroupWithOne.toAddMonoidWithOne.{0} K
    (@Ring.toAddGroupWithOne.{0} K (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K contextInstance1))))
  OddKaplansky.SourceGluing.p] (d : LocalDatum (K := K)) : 0<Fintype.card (N d) := by
  rw [Fintype.card_fin]
  have := d.rank
  omega
lemma sizes (d : LocalDatum (K := K)) : Fintype.card Small<Fintype.card (Large d) := by
  have ht := SourceFit.ratio_bound
  have hd := d.rank
  have hdpos := d_positive d
  simp only [N,Fintype.card_fin] at hdpos
  have hh := Nat.mul_le_mul_right (Fintype.card SourceFit.Slot) hd.le
  have hhh := Nat.mul_lt_mul_of_pos_right ht hdpos
  simp only [Small,Large,W,N,Fintype.card_prod,Fintype.card_fin,SourceGraph.card_vertices]
  nlinarith
end
end OddKaplansky.Construction

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.Construction
noncomputable section
local instance squareConstructionDecidableEq (α : Type portUniverse1) : DecidableEq α := Classical.decEq α
open scoped Classical BigOperators Matrix
open SourceGluing SourceGraph
local notation "M" => SourceGluing.modulus
local notation "p" => SourceGluing.p
variable {K : Type} [Field K] [Fintype K] [CharP K p]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ M)
@[instance_reducible]

def slotOrder : LinearOrder SourceFit.Slot := LinearOrder.lift' (fun s => s.val.sort) (by
  intro s t h
  apply Subtype.ext
  simpa only [Finset.sort_toFinset] using congrArg List.toFinset h)
@[instance_reducible]
def lexOrder (α : Type portUniverse2) (β : Type portUniverse3) [LinearOrder α] [LinearOrder β] : LinearOrder (α×β) :=
  LinearOrder.lift' (fun a : α×β => toLex a) (fun _ _ h => h)
def orderedIndex (α : Type portUniverse4) [LinearOrder α] [Fintype α] : α ≃ Fin (Fintype.card α) :=
  (Fintype.orderIsoFinOfCardEq α rfl).symm.toEquiv
def smallIndex : Small ≃ Fin (Fintype.card Small) := @orderedIndex Small (@lexOrder W SourceFit.Slot inferInstance slotOrder) inferInstance
def largeIndex (d : LocalDatum (K := K)) : Large d ≃ Fin (Fintype.card (Large d)) :=
  @orderedIndex (Large d) (@lexOrder Vertex (N d) inferInstance inferInstance) inferInstance
def inclusion (d : LocalDatum (K := K)) : Small → Large d := IndexCut.inclusion smallIndex (largeIndex d) (sizes d)
lemma inclusion_injective (d : LocalDatum (K := K)) : Function.Injective (inclusion d) := IndexCut.injective smallIndex (largeIndex d) (sizes d)
def extra (d : LocalDatum (K := K)) : Large d := IndexCut.extra (largeIndex d) (sizes d)
lemma inclusion_ne_extra (d : LocalDatum (K := K)) (i : Small) : inclusion d i≠extra d :=
  IndexCut.misses smallIndex (largeIndex d) (sizes d) i

def squareA (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : Matrix Small Small (R (K := K)) :=
  SquareCertificate.A (f hζ) (inclusion d) (D hζ d rect)
def squareB (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : Matrix Small Small (R (K := K)) :=
  SquareCertificate.B (f hζ) (inclusion d) (C hζ d rect)
lemma square_products (d : LocalDatum (K := K)) (rect : Rectangular hζ d) :
    squareA hζ d rect*squareB hζ d rect=1 ∧ squareB hζ d rect*squareA hζ d rect≠1 := by
  constructor
  · convert SquareCertificate.products (f hζ) (f_idem hζ) (f_commute hζ) (inclusion d) (inclusion_injective d)
      (C hζ d rect) (D hζ d rect) (C_sector hζ d rect) (D_sector hζ d rect) (DC_classical hζ d rect) using 1 <;> congr ; exact Subsingleton.elim _ _
  · convert SquareCertificate.reverse_ne (f hζ) (f_idem hζ) (f_nonzero hζ) (f_commute hζ) (inclusion d)
      (C hζ d rect) (D hζ d rect) (C_sector hζ d rect) (DC_classical hζ d rect) (extra d) (inclusion_ne_extra d) using 1 <;> congr ; exact Subsingleton.elim _ _

def A (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : Matrix (Fin (Fintype.card Small)) (Fin (Fintype.card Small)) (R (K := K)) :=
  Matrix.reindexAlgEquiv K (R (K := K)) smallIndex (squareA hζ d rect)
def B (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : Matrix (Fin (Fintype.card Small)) (Fin (Fintype.card Small)) (R (K := K)) :=
  Matrix.reindexAlgEquiv K (R (K := K)) smallIndex (squareB hζ d rect)
lemma products (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : A hζ d rect*B hζ d rect=1 ∧ B hζ d rect*A hζ d rect≠1 := by
  let E := Matrix.reindexAlgEquiv K (R (K := K)) smallIndex
  have hone : E 1=1 := map_one E
  have hmul : ∀ X Y, E (X*Y)=E X*E Y := fun X Y => map_mul E X Y
  constructor
  · change E (squareA hζ d rect)*E (squareB hζ d rect)=1
    rw [← hmul,(square_products hζ d rect).1,hone]
  · intro he
    apply (square_products hζ d rect).2
    apply E.injective
    rw [hmul,hone]
    exact he
lemma modulus_ge_two : 2≤M := by have := SourceGluing.modulus_gt; omega
def q : ℕ := FixedField.leastQ M modulus_ge_two (Fintype.card Small)
abbrev Λ := Heisenberg.GroupData M q
abbrev G := G₁×Λ
instance : Group.FG G := inferInstance

def a (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : MonoidAlgebra K G :=
  FixedField.output M modulus_ge_two (Fintype.card Small) hζ (A hζ d rect)
def b (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : MonoidAlgebra K G :=
  FixedField.output M modulus_ge_two (Fintype.card Small) hζ (B hζ d rect)
lemma scalar_products (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : a hζ d rect*b hζ d rect=1 ∧ b hζ d rect*a hζ d rect≠1 := by
  exact FixedField.output_products M modulus_ge_two (Fintype.card Small) hζ (modulus_cast (K := K))
    (A hζ d rect) (B hζ d rect) (products hζ d rect).1 (products hζ d rect).2
lemma torsion : ∃ g : G, g≠1 ∧ IsOfFinOrder g := by
  let c : Fourier.C M := Multiplicative.ofAdd (1 : ZMod M)
  have hc : c≠1 := by
    intro h
    have he : (1 : ZMod M)=0 := congrArg Multiplicative.toAdd h
    have hd : M∣1 := (ZMod.natCast_eq_zero_iff 1 M).mp (by simpa only [Nat.cast_one] using he)
    have := Nat.dvd_one.mp hd
    have := SourceGluing.modulus_gt
    omega
  let z : Λ := Heisenberg.central M q c
  have hz : z≠1 := by
    intro h
    apply hc
    apply Heisenberg.central_injective M q
    simpa only [map_one] using h
  refine ⟨(1,z),?_,?_⟩
  · intro he
    exact hz (congrArg Prod.snd he)
  · exact (MonoidHom.inr G₁ Λ).isOfFinOrder (isOfFinOrder_of_finite z)
end
end OddKaplansky.Construction

end

end OAI
end

section
namespace OAI


section
namespace OddKaplansky.Prescribed
noncomputable section
local instance prescribedDecidableEq (α : Type portUniverse1) : DecidableEq α := Classical.decEq α
open scoped Classical BigOperators
local notation "p" => SourceGluing.p
local notation "M" => SourceGluing.modulus
abbrev K := QuadraticTower.CoeffField p Construction.p_ne_two
instance : Fact (Irreducible (QuadraticTower.polynomial (QuadraticTower.xi p Construction.p_ne_two))) :=
  ⟨QuadraticTower.second_irreducible p Construction.p_ne_two Construction.minus_square⟩
instance : Field K := inferInstance
instance : Fintype K := inferInstance
instance : CharP K p :=
  charP_of_injective_ringHom ((algebraMap (QuadraticTower.FirstField p Construction.p_ne_two) K).comp
    (algebraMap (ZMod p) (QuadraticTower.FirstField p Construction.p_ne_two))).injective p
lemma card_field : Fintype.card K=p^4 := QuadraticTower.tower_card p Construction.p_ne_two

def zeta : K := @FiniteChoice.primitive K inferInstance inferInstance (QuadraticTower.fieldOrder p Construction.p_ne_two)
lemma zeta_primitive : IsPrimitiveRoot zeta M := by
  have h := @FiniteChoice.primitive_spec K inferInstance inferInstance (QuadraticTower.fieldOrder p Construction.p_ne_two)
  change IsPrimitiveRoot zeta (Fintype.card K-1) at h
  rw [card_field] at h
  simpa only [SourceGluing.modulus] using h

def localDatum : Construction.LocalDatum (K := K) := Construction.prescribedLocalDatum zeta_primitive card_field
def rectangles : Construction.Rectangular zeta_primitive localDatum := Construction.prescribedRectangles zeta_primitive localDatum
abbrev G := Construction.G
def a : MonoidAlgebra K G := Construction.a zeta_primitive localDatum rectangles
def b : MonoidAlgebra K G := Construction.b zeta_primitive localDatum rectangles
lemma products : a*b=1 ∧ b*a≠1 := Construction.scalar_products zeta_primitive localDatum rectangles
lemma torsion : ∃ g : G, g≠1 ∧ IsOfFinOrder g := Construction.torsion
lemma cellular_consequences :
    Cellular.IsCellular (Cellular.operator b) ∧ Function.Injective (Cellular.operator b) ∧
    ¬Function.Surjective (Cellular.operator b) ∧
    Set.range (Cellular.operator b)={y | Cellular.operator (b*a) y=y} ∧
    ∃ h : G, (b*a-1).coeff h ≠ 0 ∧ Pi.single h 1 ∉ Set.range (Cellular.operator b) := by
  obtain ⟨hcell,hinj,hnonsurj,hrange,h,hh,hm⟩ := Cellular.theorem_all_configurations a b products.1 products.2
  refine ⟨hcell,hinj,hnonsurj,hrange,h,hh,?_⟩
  have hdelta : @Pi.single G (fun _ => K) (fun _ => inferInstance) (Classical.decEq G) h 1 = (Pi.single h 1 : G → K) := by
    funext g
    by_cases hg : g=h <;> simp only [hg, Pi.single_eq_same, ne_eq, not_false_eq_true, Pi.single_eq_of_ne]
  rw [← hdelta]
  exact hm
end
end OddKaplansky.Prescribed

namespace OddKaplansky
noncomputable section
local instance mainEndpointDecidableEq (α : Type portUniverse2) : DecidableEq α := Classical.decEq α
open scoped Classical

def cellular {K G : Type} [Field K] [Group G]
    (d : MonoidAlgebra K G) (x : G → K) (g : G) : K :=
  d.coeff.sum fun u c => c * x (g * u)
lemma cellular_eq_operator {K G : Type} [Field K] [Group G] (d : MonoidAlgebra K G) :
    cellular d=Cellular.operator d := by
  funext x g
  exact (Cellular.operator_formula d x g).symm

def MainClaim : Prop :=
  sourcePrime.Prime ∧ Odd sourcePrime ∧
  ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K sourcePrime),
    Fintype.card K = sourcePrime^4 ∧
    ∃ (G : Type) (_ : Group G) (_ : Group.FG G),
      (∃ g : G, g ≠ 1 ∧ IsOfFinOrder g) ∧
      ∃ a b : MonoidAlgebra K G,
        a * b = 1 ∧ b * a ≠ 1 ∧
        Function.Injective (cellular b) ∧ ¬ Function.Surjective (cellular b)

theorem main_theorem : MainClaim := by
  let : CharP Prescribed.K sourcePrime := by rw [← SourceGluing.p_def]; infer_instance
  refine ⟨sourcePrime_prime,sourcePrime_odd,Prescribed.K,inferInstance,inferInstance,inferInstance,?_,
    Prescribed.G,inferInstance,inferInstance,Prescribed.torsion,Prescribed.a,Prescribed.b,
    Prescribed.products.1,Prescribed.products.2,?_,?_⟩
  · rw [Prescribed.card_field,SourceGluing.p_def]
  · rw [cellular_eq_operator]
    exact Prescribed.cellular_consequences.2.1
  · rw [cellular_eq_operator]
    exact Prescribed.cellular_consequences.2.2.1

end
end OddKaplansky

end

end OAI
end

section
/-! Transfer of OpenAI's `OAI.OddKaplansky.main_theorem` (OpenAI Math Release, "A Counterexample
to Kaplansky's Direct-Finiteness Conjecture in Odd Characteristic", https://github.com/openai/math)
to the published `GottschalkSurjunctivity.IsSurjunctive`: OpenAI's injective, non-surjective
map `cellular b` on `K^G` (`K` a finite field) is continuous and shift-equivariant. -/

namespace GottschalkSurjunctivity.OAIBridge

/-- OpenAI's `cellular d` is continuous for the product of discrete topologies. -/
theorem cellular_continuous {K G : Type} [Field K] [Group G] [TopologicalSpace K]
    [DiscreteTopology K] (d : MonoidAlgebra K G) :
    Continuous (OAI.OddKaplansky.cellular d) := by
  have : ContinuousAdd K := ⟨continuous_of_discreteTopology⟩
  refine continuous_pi fun g => ?_
  show Continuous fun x : G → K => ∑ u ∈ d.coeff.support, d.coeff u * x (g * u)
  exact continuous_finsetSum _ fun u _ =>
    (continuous_of_discreteTopology (f := fun c : K => d.coeff u * c)).comp (continuous_apply _)

/-- OpenAI's `cellular d` commutes with the left shift. -/
theorem cellular_equivariant {K G : Type} [Field K] [Group G] (d : MonoidAlgebra K G) :
    IsShiftEquivariant G (OAI.OddKaplansky.cellular d) := by
  intro g x
  funext h
  simp only [OAI.OddKaplansky.cellular, shift, mul_assoc]

/-- Gottschalk's surjunctivity conjecture fails. -/
theorem not_gottschalk : ¬ ∀ (G : Type) [Group G], IsSurjunctive G := by
  intro hall
  obtain ⟨-, -, K, _, _, _, -, G, _, _, -, -, b, -, -, hinj, hns⟩ :=
    OAI.OddKaplansky.main_theorem
  let : TopologicalSpace K := ⊥
  have : DiscreteTopology K := ⟨rfl⟩
  exact hns (hall G K (OAI.OddKaplansky.cellular b) (cellular_continuous b)
    (cellular_equivariant b) hinj)

end GottschalkSurjunctivity.OAIBridge
end

theorem solution : ¬ ∀ (G : Type) [Group G], GottschalkSurjunctivity.IsSurjunctive G :=
  GottschalkSurjunctivity.OAIBridge.not_gottschalk
