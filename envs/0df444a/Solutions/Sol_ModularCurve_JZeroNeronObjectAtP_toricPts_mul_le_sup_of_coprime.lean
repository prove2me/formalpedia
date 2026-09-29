-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.toricPts_mul_le_sup_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/f5d73ec6-0146-559a-bea1-87c24faa990b

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_toricPts_mul_le_sup_of_coprime

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

noncomputable section
namespace E2H4le
namespace Ws31

section conv

variable {S : Type} [CommRing S] {L : Type} [CommRing L] [Algebra S L] {G : Type} [AddMonoid G]

theorem convMul_apply_single (c c' : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (v : G) :
    (c * c') (AddMonoidAlgebra.single v 1) =
      c (AddMonoidAlgebra.single v 1) * c' (AddMonoidAlgebra.single v 1) := by
  rw [AlgHom.convMul_apply, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
    Algebra.TensorProduct.lift_tmul]
  simp

theorem convOne_apply_single (v : G) :
    (1 : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (AddMonoidAlgebra.single v 1) = 1 := by
  rw [AlgHom.convOne_apply, AddMonoidAlgebra.counit_single, CommSemiring.counit_apply, map_one]

theorem convPow_apply_single (c : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (v : G) (n : ℕ) :
    (c ^ n) (AddMonoidAlgebra.single v 1) = c (AddMonoidAlgebra.single v 1) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, convOne_apply_single]
  | succ n ih => rw [pow_succ, convMul_apply_single, ih, pow_succ]

theorem conv_ext {c c' : WithConv (AddMonoidAlgebra S G →ₐ[S] L)}
    (h : ∀ v, c (AddMonoidAlgebra.single v 1) = c' (AddMonoidAlgebra.single v 1)) : c = c' := by
  have : c.ofConv = c'.ofConv := AddMonoidAlgebra.algHom_ext h (Algebra.ext_id _ _ _)
  exact congrArg WithConv.toConv this

theorem convPow_eq_one (c : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (n : ℕ) (hn : ∀ v : G, n • v = 0) :
    c ^ n = 1 := by
  refine conv_ext (fun v => ?_)
  rw [convPow_apply_single, convOne_apply_single, ← map_pow, AddMonoidAlgebra.single_pow, hn, one_pow]
  exact map_one c.ofConv

end conv

theorem castOver_mul {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {ι ι' : T ⟶ Spec (CommRingCat.of R)} (h : ι = ι') (x y : SchemeHomOver ι f) :
    castOver h (L.mul ι x y) = L.mul ι' (castOver h x) (castOver h y) := by
  subst h; rfl

section toric

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p} {Λ : LevelData N₀ p A}
  (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)

theorem genOfBaseChangePt_mul
    (y y' : SchemeHomOver (barPt A) (RelativeGroupLaw.baseChangeStr Λ.σA O.g)) :
    genOfBaseChangePt Λ.hσA ((O.L.baseChange Λ.σA).mul _ y y') =
      O.L.mul _ (genOfBaseChangePt Λ.hσA y) (genOfBaseChangePt Λ.hσA y') := by
  unfold genOfBaseChangePt
  rw [RelativeGroupLaw.baseChangePointToBase_mul]
  exact castOver_mul O.L Λ.hσA _ _

theorem toricPoint_mul {m : ℕ} (hm : 0 < m)
    (χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)) :
    O.toricPoint m hm (χ * χ').ofConv = O.toricPoint m hm χ.ofConv + O.toricPoint m hm χ'.ofConv := by
  apply O.pts.injective
  rw [O.pts_add]
  unfold toricPoint
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, O.toricLift_mul m hm χ χ',
    genOfBaseChangePt_mul]

def toricPointHom {m : ℕ} (hm : 0 < m) :
    WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) →* Multiplicative (JZero (N₀ * p)) where
  toFun χ := Multiplicative.ofAdd (O.toricPoint m hm χ.ofConv)
  map_one' := by
    have h := toricPoint_mul O hm 1 1
    rw [mul_one] at h
    have h0 : O.toricPoint m hm
        (1 : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)).ofConv = 0 := by
      have := congrArg (fun z => z - O.toricPoint m hm
        (1 : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)).ofConv) h
      simpa using this.symm
    rw [h0]; rfl
  map_mul' χ χ' := by rw [← ofAdd_add, ← toricPoint_mul]

theorem nsmul_toricPoint_eq_zero {m : ℕ} (hm : 0 < m) (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) :
    m • O.toricPoint m hm χ = 0 := by
  have h := (toricPointHom O hm).map_pow (WithConv.toConv χ) m
  rw [convPow_eq_one _ m (fun v => ?_), map_one] at h
  ·
    have h' := congrArg Multiplicative.toAdd h
    simpa [toricPointHom] using h'.symm
  ·
    funext i; simp

end toric

end E2H4le.Ws31

namespace E2H4le

open CategoryTheory.Limits

section CharBound

variable {t m : ℕ} [NeZero m] {M : Type} [CommMonoid M]

theorem ofAdd_eq_prod_pow (v : Fin t → ZMod m) :
    Multiplicative.ofAdd v = ∏ i, (Multiplicative.ofAdd (Pi.single i (1 : ZMod m))) ^ (v i).val := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [ofAdd_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← ofAdd_nsmul, ← Pi.single_smul', nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

theorem monoidHom_ext_single {φ ψ : Multiplicative (Fin t → ZMod m) →* M}
    (h : ∀ i, φ (Multiplicative.ofAdd (Pi.single i 1)) = ψ (Multiplicative.ofAdd (Pi.single i 1))) : φ = ψ := by
  refine MonoidHom.ext (fun x => ?_)
  obtain ⟨v, rfl⟩ := Multiplicative.ofAdd.surjective x
  rw [ofAdd_eq_prod_pow, map_prod, map_prod]
  exact Finset.prod_congr rfl (fun i _ => by rw [map_pow, map_pow, h i])

theorem pow_m_eq_one (φ : Multiplicative (Fin t → ZMod m) →* M) (x : Multiplicative (Fin t → ZMod m)) :
    φ x ^ m = 1 := by
  rw [← map_pow]
  have hx : x ^ m = 1 := by
    change Multiplicative.ofAdd (m • Multiplicative.toAdd x) = Multiplicative.ofAdd 0
    congr 1
    funext i; simp
  rw [hx, map_one]

end CharBound

section AlgHomBound

variable (S : Type) [CommRing S] (L : Type) [CommRing L] [IsDomain L] [Algebra S L] (t m : ℕ) [NeZero m]

def rootsOf (χ : AddMonoidAlgebra S (Fin t → ZMod m) →ₐ[S] L) : Fin t → rootsOfUnity m L := fun i =>
  rootsOfUnity.mkOfPowEq (((AddMonoidAlgebra.lift S L (Fin t → ZMod m)).symm χ) (Multiplicative.ofAdd (Pi.single i 1)))
    (pow_m_eq_one _ _)

theorem rootsOf_injective : Function.Injective (rootsOf S L t m) := by
  intro χ χ' h
  apply (AddMonoidAlgebra.lift S L (Fin t → ZMod m)).symm.injective
  refine monoidHom_ext_single (fun i => ?_)
  have h1 := congrArg (fun f => (((f i : rootsOfUnity m L) : Lˣ) : L)) h
  simpa only [rootsOf, rootsOfUnity.val_mkOfPowEq_coe] using h1

theorem natCard_algHom_le : Nat.card (AddMonoidAlgebra S (Fin t → ZMod m) →ₐ[S] L) ≤ m ^ t := by
  classical
  calc Nat.card (AddMonoidAlgebra S (Fin t → ZMod m) →ₐ[S] L)
      ≤ Nat.card (Fin t → rootsOfUnity m L) := Nat.card_le_card_of_injective _ (rootsOf_injective S L t m)
    _ = Nat.card (rootsOfUnity m L) ^ t := by rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin t), Fintype.card_fin]
    _ ≤ m ^ t := Nat.pow_le_pow_left (card_rootsOfUnity L m) t

theorem finite_algHom : Finite (AddMonoidAlgebra S (Fin t → ZMod m) →ₐ[S] L) := by
  classical
  exact Finite.of_injective _ (rootsOf_injective S L t m)

end AlgHomBound

section Range

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p} {Λ : LevelData N₀ p A}
  (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)

theorem nsmul_toricPoint_mem_range {m : ℕ} (hm : 0 < m)
    (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) (n : ℕ) :
    n • O.toricPoint m hm χ ∈ Set.range (O.toricPoint m hm) := by
  refine ⟨((WithConv.toConv χ) ^ n).ofConv, ?_⟩
  have h := congrArg Multiplicative.toAdd ((Ws31.toricPointHom O hm).map_pow (WithConv.toConv χ) n)
  simpa [Ws31.toricPointHom] using h

def rangeSubgroup {m : ℕ} (hm : 0 < m) : AddSubgroup (JZero (N₀ * p)) where
  carrier := Set.range (O.toricPoint m hm)
  add_mem' := by
    rintro _ _ ⟨χ, rfl⟩ ⟨χ', rfl⟩
    exact ⟨(WithConv.toConv χ * WithConv.toConv χ').ofConv, Ws31.toricPoint_mul O hm _ _⟩
  zero_mem' := ⟨(1 : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)).ofConv, by
    have h := (Ws31.toricPointHom O hm).map_one
    exact congrArg Multiplicative.toAdd h⟩
  neg_mem' := by
    rintro _ ⟨χ, rfl⟩
    have h0 : (m - 1) • O.toricPoint m hm χ + O.toricPoint m hm χ = 0 := by
      rw [← succ_nsmul, Nat.sub_add_cancel hm, Ws31.nsmul_toricPoint_eq_zero O hm χ]
    rw [← (eq_neg_of_add_eq_zero_left h0)]
    exact nsmul_toricPoint_mem_range O hm χ (m - 1)

theorem toricPts_eq_rangeSubgroup {m : ℕ} (hm : 0 < m) : O.toricPts m = rangeSubgroup O hm := by
  apply le_antisymm
  · rw [toricPts, dif_pos hm, AddSubgroup.closure_le]
    exact fun x hx => hx
  · intro x hx
    rw [toricPts, dif_pos hm]
    exact AddSubgroup.subset_closure hx

theorem natCard_toricPts_le {m : ℕ} (hm : 0 < m) : Nat.card ↥(O.toricPts m) ≤ m ^ O.toricRank := by
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI := finite_algHom (↥A) (AlgebraicClosure ℚ) O.toricRank m
  rw [toricPts_eq_rangeSubgroup O hm]
  calc Nat.card ↥(rangeSubgroup O hm)
      = Nat.card (Set.range (O.toricPoint m hm)) := rfl
    _ ≤ Nat.card (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) :=
        Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    _ ≤ m ^ O.toricRank := natCard_algHom_le (↥A) (AlgebraicClosure ℚ) O.toricRank m

end Range

end E2H4le

namespace E2H4

section Characters

variable (S : Type) [CommRing S] {L : Type} [Field L] [Algebra S L] {t m : ℕ}

def dot (a v : Fin t → ZMod m) : ZMod m := ∑ i, a i * v i

theorem dot_add (a v w : Fin t → ZMod m) : dot a (v + w) = dot a v + dot a w := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot_zero (a : Fin t → ZMod m) : dot a 0 = 0 := by
  simp [dot]

theorem dot_single [DecidableEq (Fin t)] (a : Fin t → ZMod m) (i : Fin t) : dot a (Pi.single i 1) = a i := by
  classical
  simp only [dot, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

variable [NeZero m] {ζ : L} (hζ : ζ ^ m = 1)
include hζ

theorem pow_val_add (x y : ZMod m) : ζ ^ (x + y).val = ζ ^ x.val * ζ ^ y.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (x.val + y.val) m, pow_add, pow_mul, hζ, one_pow, mul_one]

noncomputable def chi (a : Fin t → ZMod m) : Multiplicative (Fin t → ZMod m) →* L where
  toFun v := ζ ^ (dot a (Multiplicative.toAdd v)).val
  map_one' := by
    show ζ ^ (dot a (0 : Fin t → ZMod m)).val = 1
    rw [dot_zero, ZMod.val_zero, pow_zero]
  map_mul' v w := by
    show ζ ^ (dot a (Multiplicative.toAdd v + Multiplicative.toAdd w)).val = _
    rw [dot_add, pow_val_add hζ]

theorem chi_apply (a v : Fin t → ZMod m) : chi hζ a (Multiplicative.ofAdd v) = ζ ^ (dot a v).val := rfl

noncomputable def character (a : Fin t → ZMod m) : AddMonoidAlgebra S (Fin t → ZMod m) →ₐ[S] L :=
  AddMonoidAlgebra.lift S L (Fin t → ZMod m) (chi hζ a)

theorem character_single (a v : Fin t → ZMod m) :
    character S hζ a (AddMonoidAlgebra.single v 1) = ζ ^ (dot a v).val := by
  rw [character, AddMonoidAlgebra.lift_single, one_smul]
  rfl

omit hζ in

theorem character_injective (hprim : IsPrimitiveRoot ζ m) :
    Function.Injective (character S (t := t) hprim.pow_eq_one) := by
  classical
  intro a b hab
  funext i
  have h := congrArg (fun χ => χ (AddMonoidAlgebra.single (Pi.single i 1) 1)) hab
  simp only [character_single, dot_single] at h
  exact ZMod.val_injective m (hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h)

end Characters

theorem exists_isPrimitiveRoot (m : ℕ) (hm : 0 < m) : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ m := by
  haveI : NeZero (m : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hm.ne'⟩
  have hdeg : (Polynomial.cyclotomic m (AlgebraicClosure ℚ)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr hm).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).mp hζ⟩

end E2H4

namespace DivTower

open E2H4le E2H4le.Ws31

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p} {Λ : LevelData N₀ p A}
  (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)

abbrev redHom (t : ℕ) {m m' : ℕ} (h : m ∣ m') : (Fin t → ZMod m') →+ (Fin t → ZMod m) :=
  AddMonoidHom.pi fun i => ((ZMod.castHom h (ZMod m)).toAddMonoidHom).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ZMod m') i)

abbrev redAlg (t : ℕ) {m m' : ℕ} (h : m ∣ m') : muCoord ↥A t m' →ₐ[↥A] muCoord ↥A t m :=
  AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (redHom t h)

theorem toricPoint_eq_toricPoint_comp {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m') (h : m ∣ m')
    (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) :
    O.toricPoint m hm χ = O.toricPoint m' hm' (χ.comp (redAlg (A := A) O.toricRank h)) := by
  unfold toricPoint
  congr 2
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe]
  change Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ (O.toricLift m hm).1 =
    Spec.map (CommRingCat.ofHom (χ.comp (redAlg (A := A) O.toricRank h)).toRingHom) ≫ (O.toricLift m' hm').1
  rw [← O.toricLift_compat m m' hm hm' h, ← Category.assoc]
  congr 1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem character_surjective {m : ℕ} [NeZero m] {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ m) (t : ℕ) :
    Function.Surjective (E2H4.character (↥A) (t := t) hζ.pow_eq_one) := by
  classical
  haveI := E2H4le.finite_algHom (↥A) (AlgebraicClosure ℚ) t m
  refine (Function.Injective.bijective_of_nat_card_le (E2H4.character_injective (↥A) hζ) ?_).2
  calc Nat.card (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ)
      ≤ m ^ t := E2H4le.natCard_algHom_le (↥A) (AlgebraicClosure ℚ) t m
    _ = Nat.card (Fin t → ZMod m) := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card, ZMod.card, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem pow_mul_eq_pow_pow_mod {ξ : AlgebraicClosure ℚ} {m d : ℕ} (hξ : ξ ^ (m * d) = 1) (n : ℕ) :
    ξ ^ (d * n) = (ξ ^ d) ^ (n % m) := by
  have h : d * n = d * (n % m) + (m * d) * (n / m) := by
    conv_lhs => rw [← Nat.mod_add_div n m]
    ring
  rw [h, pow_add, pow_mul, pow_mul, hξ, one_pow, mul_one]

end DivTower

namespace CrtSplit

open E2H4le E2H4le.Ws31 DivTower

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p} {Λ : LevelData N₀ p A}
  (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)

theorem pow_mod_of_pow_eq_one {ξ : AlgebraicClosure ℚ} {N : ℕ} (h : ξ ^ N = 1) (s : ℕ) : ξ ^ (s % N) = ξ ^ s := by
  conv_rhs => rw [← Nat.mod_add_div s N, pow_add, pow_mul, h, one_pow, mul_one]

theorem dot_add_left {t m : ℕ} (a b v : Fin t → ZMod m) : E2H4.dot (a + b) v = E2H4.dot a v + E2H4.dot b v := by
  simp only [E2H4.dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dot_mul_left {t m : ℕ} (k : ZMod m) (a v : Fin t → ZMod m) :
    E2H4.dot (fun i => k * a i) v = k * E2H4.dot a v := by
  simp only [E2H4.dot, Finset.mul_sum, mul_assoc]

theorem character_add {t m : ℕ} [NeZero m] {ξ : AlgebraicClosure ℚ} (hξ : ξ ^ m = 1) (a b : Fin t → ZMod m) :
    WithConv.toConv (E2H4.character (↥A) hξ (a + b)) =
      WithConv.toConv (E2H4.character (↥A) hξ a) * WithConv.toConv (E2H4.character (↥A) hξ b) := by
  refine Ws31.conv_ext (fun v => ?_)
  rw [Ws31.convMul_apply_single]
  change E2H4.character (↥A) hξ (a + b) (AddMonoidAlgebra.single v 1) =
    E2H4.character (↥A) hξ a (AddMonoidAlgebra.single v 1) * E2H4.character (↥A) hξ b (AddMonoidAlgebra.single v 1)
  rw [E2H4.character_single, E2H4.character_single, E2H4.character_single, dot_add_left, E2H4.pow_val_add hξ]

theorem character_mul_eq_comp {t N n : ℕ} [NeZero N] [NeZero n] (h : n ∣ N) (k : ℕ) (hk : N = k * n)
    {ξ : AlgebraicClosure ℚ} (hξ : ξ ^ N = 1) (hξk : (ξ ^ k) ^ n = 1) (e : Fin t → ZMod N) :
    E2H4.character (↥A) hξ (fun i => (k : ZMod N) * e i) =
      (E2H4.character (↥A) hξk (redHom t h e)).comp (redAlg (A := A) t h) := by
  refine AddMonoidAlgebra.algHom_ext (fun v => ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply]
  have hred : redAlg (A := A) t h (AddMonoidAlgebra.single v 1) = AddMonoidAlgebra.single (redHom t h v) 1 :=
    AddMonoidAlgebra.mapDomain_single
  rw [hred, E2H4.character_single, E2H4.character_single, dot_mul_left]

  set X := E2H4.dot e v with hX
  have hdot : (ZMod.castHom h (ZMod n)) X = E2H4.dot (redHom t h e) (redHom t h v) := by
    simp only [hX, E2H4.dot, map_sum, map_mul]
    rfl
  rw [← hdot, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, pow_mod_of_pow_eq_one hξk, ← pow_mul,
    ZMod.val_mul, ZMod.val_natCast, pow_mod_of_pow_eq_one hξ, ← pow_mod_of_pow_eq_one hξ (k % N * X.val),
    Nat.mod_mul_mod, pow_mod_of_pow_eq_one hξ]

theorem main (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    O.toricPts (a * b) ≤ O.toricPts a ⊔ O.toricPts b := by
  classical
  have habp : 0 < a * b := Nat.mul_pos ha hb
  haveI : NeZero a := ⟨ha.ne'⟩
  haveI : NeZero b := ⟨hb.ne'⟩
  haveI : NeZero (a * b) := ⟨habp.ne'⟩
  intro x hx
  rw [toricPts_eq_rangeSubgroup O habp] at hx
  obtain ⟨χ, rfl⟩ : x ∈ Set.range (O.toricPoint (a * b) habp) := hx
  obtain ⟨ξ, hξ⟩ := E2H4.exists_isPrimitiveRoot (a * b) habp
  obtain ⟨c, rfl⟩ := character_surjective (A := A) hξ O.toricRank χ

  obtain ⟨u, w, huw⟩ : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hab
  let c₁ : Fin O.toricRank → ZMod (a * b) := fun i => (b : ZMod (a * b)) * ((w : ZMod (a * b)) * c i)
  let c₂ : Fin O.toricRank → ZMod (a * b) := fun i => (a : ZMod (a * b)) * ((u : ZMod (a * b)) * c i)
  have hsplit : c = c₁ + c₂ := by
    funext i
    have h1 : ((u : ZMod (a * b)) * a + w * b) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ZMod (a * b)) huw
    change c i = (b : ZMod (a * b)) * (w * c i) + a * (u * c i)
    linear_combination (-(c i)) * h1

  have hξa : (ξ ^ b) ^ a = 1 := by rw [← pow_mul, mul_comm, hξ.pow_eq_one]
  have hξb : (ξ ^ a) ^ b = 1 := by rw [← pow_mul, hξ.pow_eq_one]
  have h₁ : E2H4.character (↥A) hξ.pow_eq_one c₁ =
      (E2H4.character (↥A) hξa (redHom O.toricRank (Dvd.intro b rfl) (fun i => (w : ZMod (a * b)) * c i))).comp
        (redAlg (A := A) O.toricRank (Dvd.intro b rfl)) :=
    character_mul_eq_comp (A := A) (Dvd.intro b rfl) b (mul_comm a b) hξ.pow_eq_one hξa _
  have h₂ : E2H4.character (↥A) hξ.pow_eq_one c₂ =
      (E2H4.character (↥A) hξb (redHom O.toricRank (Dvd.intro_left a rfl) (fun i => (u : ZMod (a * b)) * c i))).comp
        (redAlg (A := A) O.toricRank (Dvd.intro_left a rfl)) :=
    character_mul_eq_comp (A := A) (Dvd.intro_left a rfl) a rfl hξ.pow_eq_one hξb _

  rw [hsplit]
  have hmul : O.toricPoint (a * b) habp (E2H4.character (↥A) hξ.pow_eq_one (c₁ + c₂)) =
      O.toricPoint (a * b) habp (E2H4.character (↥A) hξ.pow_eq_one c₁) +
        O.toricPoint (a * b) habp (E2H4.character (↥A) hξ.pow_eq_one c₂) := by
    have h := Ws31.toricPoint_mul O habp (WithConv.toConv (E2H4.character (↥A) hξ.pow_eq_one c₁))
      (WithConv.toConv (E2H4.character (↥A) hξ.pow_eq_one c₂))
    rw [← character_add] at h
    exact h
  rw [hmul]
  refine AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left ?_) (AddSubgroup.mem_sup_right ?_)
  · rw [h₁, ← toricPoint_eq_toricPoint_comp O ha habp, toricPts_eq_rangeSubgroup O ha]
    exact ⟨_, rfl⟩
  · rw [h₂, ← toricPoint_eq_toricPoint_comp O hb habp, toricPts_eq_rangeSubgroup O hb]
    exact ⟨_, rfl⟩

end CrtSplit

end

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    O.toricPts (a * b) ≤ O.toricPts a ⊔ O.toricPts b := by
  exact CrtSplit.main O a b ha hb hab

end S_ModularCurve_JZeroNeronObjectAtP_toricPts_mul_le_sup_of_coprime
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_toricPts_mul_le_sup_of_coprime (solution)
