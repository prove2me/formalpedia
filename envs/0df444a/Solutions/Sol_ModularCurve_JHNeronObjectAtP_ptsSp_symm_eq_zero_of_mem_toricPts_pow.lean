-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.ptsSp_symm_eq_zero_of_mem_toricPts_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/7e37bd64-6bca-560b-bafe-92fd87251c5a

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_nodeUnit_eq_residue_toricLift_and_mul_and_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_eq_zero_of_mem_toricPts_pow

set_option autoImplicit false
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing
open ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

open AddMonoidAlgebra

namespace N4Alg

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (t m : ℕ)

private abbrev _root_.N4Alg.G : Type := Fin t → ZMod m

p2m_export "N4Alg" "G"

theorem nsmul_eq_zero (v : G t m) : m • v = 0 := by
  funext i
  simp [nsmul_eq_mul]

theorem single_one_pow_eq_one {k : Type*} [CommSemiring k] (v : G t m) :
    (single v (1 : k) : AddMonoidAlgebra k (G t m)) ^ m = 1 := by
  rw [AddMonoidAlgebra.single_pow, one_pow, nsmul_eq_zero, AddMonoidAlgebra.one_def]

theorem apply_single_mem (hm : 0 < m) (χ : AddMonoidAlgebra A (G t m) →ₐ[A] AlgebraicClosure ℚ) (v : G t m) :
    χ (single v 1) ∈ A := by
  set u := χ (single v 1) with hu
  have hum : u ^ m = 1 := by
    rw [hu, ← map_pow, single_one_pow_eq_one, map_one]
  have hint : IsIntegral A u := IsIntegral.of_pow hm (by rw [hum]; exact isIntegral_one)
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := AlgebraicClosure ℚ)).mp hint
  rw [← hy]
  exact y.2

noncomputable def charHom (hm : 0 < m) (χ : AddMonoidAlgebra A (G t m) →ₐ[A] AlgebraicClosure ℚ) :
    Multiplicative (G t m) →* A where
  toFun v := ⟨χ (single (Multiplicative.toAdd v) 1), apply_single_mem A t m hm χ _⟩
  map_one' := by
    apply Subtype.ext
    show χ (single (Multiplicative.toAdd 1) 1) = ((1 : A) : AlgebraicClosure ℚ)
    rw [toAdd_one, ← AddMonoidAlgebra.one_def, map_one, OneMemClass.coe_one]
  map_mul' a b := by
    apply Subtype.ext
    show χ (single (Multiplicative.toAdd (a * b)) 1) =
      ((⟨χ (single (Multiplicative.toAdd a) 1), _⟩ * ⟨χ (single (Multiplicative.toAdd b) 1), _⟩ : A) : AlgebraicClosure ℚ)
    rw [MulMemClass.coe_mul, toAdd_mul, ← map_mul, AddMonoidAlgebra.single_mul_single, mul_one]

theorem coe_charHom_apply (hm : 0 < m) (χ : AddMonoidAlgebra A (G t m) →ₐ[A] AlgebraicClosure ℚ) (v : Multiplicative (G t m)) :
    ((charHom A t m hm χ v : A) : AlgebraicClosure ℚ) = χ (single (Multiplicative.toAdd v) 1) := rfl

noncomputable def liftA (hm : 0 < m) (χ : AddMonoidAlgebra A (G t m) →ₐ[A] AlgebraicClosure ℚ) :
    AddMonoidAlgebra A (G t m) →ₐ[A] A :=
  AddMonoidAlgebra.lift A A (G t m) (charHom A t m hm χ)

theorem liftA_single (hm : 0 < m) (χ : AddMonoidAlgebra A (G t m) →ₐ[A] AlgebraicClosure ℚ) (v : G t m) (b : A) :
    liftA A t m hm χ (single v b) = b * charHom A t m hm χ (Multiplicative.ofAdd v) := by
  rw [liftA, AddMonoidAlgebra.lift_single, smul_eq_mul]

theorem ofId_comp_liftA (hm : 0 < m) (χ : AddMonoidAlgebra A (G t m) →ₐ[A] AlgebraicClosure ℚ) :
    (Algebra.ofId A (AlgebraicClosure ℚ)).comp (liftA A t m hm χ) = χ := by
  refine AddMonoidAlgebra.algHom_ext (fun v => ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, liftA_single, one_mul, Algebra.ofId_apply]
  exact coe_charHom_apply A t m hm χ (Multiplicative.ofAdd v)

theorem algebraMap_comp_liftA (hm : 0 < m) (χ : AddMonoidAlgebra A (G t m) →ₐ[A] AlgebraicClosure ℚ) :
    (algebraMap A (AlgebraicClosure ℚ)).comp (liftA A t m hm χ).toRingHom = χ.toRingHom := by
  have h := congrArg AlgHom.toRingHom (ofId_comp_liftA A t m hm χ)
  exact h

theorem subtype_comp_liftA (hm : 0 < m) (χ : AddMonoidAlgebra A (G t m) →ₐ[A] AlgebraicClosure ℚ) :
    A.subtype.comp (liftA A t m hm χ).toRingHom = χ.toRingHom :=
  algebraMap_comp_liftA A t m hm χ

theorem coe_liftA_apply (hm : 0 < m) (χ : AddMonoidAlgebra A (G t m) →ₐ[A] AlgebraicClosure ℚ) (x : AddMonoidAlgebra A (G t m)) :
    ((liftA A t m hm χ x : A) : AlgebraicClosure ℚ) = χ x := by
  have := congrArg (fun f : AddMonoidAlgebra A (G t m) →ₐ[A] AlgebraicClosure ℚ => f x) (ofId_comp_liftA A t m hm χ)
  exact this

noncomputable def triv : AddMonoidAlgebra A (G t m) →ₐ[A] A :=
  AddMonoidAlgebra.lift A A (G t m) 1

theorem triv_single (v : G t m) (b : A) : triv A t m (single v b) = b := by
  rw [triv, AddMonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one]

theorem residue_comp_liftA_eq (p n : ℕ) [Fact p.Prime] (hmp : m = p ^ n)
    [CharP (IsLocalRing.ResidueField A) p]
    (χ : AddMonoidAlgebra A (G t m) →ₐ[A] AlgebraicClosure ℚ) :
    haveI hm : 0 < m := hmp ▸ pow_pos (Fact.out : p.Prime).pos n
    (IsLocalRing.residue A).comp (liftA A t m hm χ).toRingHom = (IsLocalRing.residue A).comp (triv A t m).toRingHom := by
  have hm : 0 < m := hmp ▸ pow_pos (Fact.out : p.Prime).pos n
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) (fun v => ?_)
  · show IsLocalRing.residue A (liftA A t m hm χ (single 0 b)) = IsLocalRing.residue A (triv A t m (single 0 b))
    rw [liftA_single, triv_single, ofAdd_zero, map_one, mul_one]
  · show IsLocalRing.residue A (liftA A t m hm χ (single v 1)) = IsLocalRing.residue A (triv A t m (single v 1))
    rw [liftA_single, triv_single, one_mul, map_one]
    set r := IsLocalRing.residue A (charHom A t m hm χ (Multiplicative.ofAdd v)) with hr
    have h1 : (Multiplicative.ofAdd v) ^ (p ^ n) = 1 := by
      rw [← ofAdd_nsmul, ← hmp, nsmul_eq_zero, ofAdd_zero]
    have h2 : charHom A t m hm χ (Multiplicative.ofAdd v) ^ (p ^ n) = 1 := by
      rw [← map_pow, h1, map_one]
    have hrm : r ^ (p ^ n) = 1 := by
      simp only [hr, ← map_pow, h2, map_one]
    have hsub : (r - 1) ^ (p ^ n) = 0 := by
      rw [sub_pow_char_pow, hrm, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (pow_pos (Fact.out : p.Prime).pos n).ne' |>.mp hsub)

open WithConv in
theorem ofConv_one : (WithConv.ofConv (1 : WithConv (AddMonoidAlgebra A (G t m) →ₐ[A] A))) = triv A t m := by
  refine AddMonoidAlgebra.algHom_ext (fun v => ?_) (Subsingleton.elim _ _)
  rw [triv_single]
  show (1 : WithConv (AddMonoidAlgebra A (G t m) →ₐ[A] A)) (single v 1) = 1
  rw [AlgHom.convOne_apply, AddMonoidAlgebra.counit_single]
  simp

open WithConv in
theorem toConv_triv : WithConv.toConv (triv A t m) = (1 : WithConv (AddMonoidAlgebra A (G t m) →ₐ[A] A)) := by
  rw [← ofConv_one]

open WithConv in
theorem triv_convMul_triv :
    (WithConv.toConv (triv A t m) * WithConv.toConv (triv A t m)).ofConv = triv A t m := by
  rw [toConv_triv, one_mul, ofConv_one]

end N4Alg

noncomputable section

open IsLocalRing

namespace N4Aux

theorem isDominant_barPt (A : ValuationSubring (AlgebraicClosure ℚ)) : IsDominant (barPt A) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap A.subtype)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective]
  exact bot_le

theorem specMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

end N4Aux

open N4Aux

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (n : ℕ) (hn : 0 < n) (x : JH M H) (hx : x ∈ O.toricPts (p ^ n))
    (s : SchemeHomOver Λ.σA O.g) (hs : (O.pts x).1 = barPt A ≫ s.1)
    (sκ : SchemeHomOver (resPt A ≫ Λ.σA) O.g) (hsκ : sκ.1 = resPt A ≫ s.1) :
    O.ptsSp.symm sκ = 0 := by

  have hm : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  haveI := isDominant_barPt A
  haveI : IsSeparated O.g := O.separated

  obtain ⟨-, -, hmem, -⟩ :=
    ModularCurve.JHNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
      p M H hpM A hA Λ O (p ^ n) hm
  obtain ⟨χ, hχ⟩ := (hmem x).mp hx

  set χA := N4Alg.liftA A O.toricRank (p ^ n) hm χ with hχA
  let s'1 : Spec (CommRingCat.of ↥A) ⟶ O.G :=
    Spec.map (CommRingCat.ofHom χA.toRingHom) ≫ (O.toricLift (p ^ n) hm).1 ≫ pullback.fst O.g Λ.σA
  have hlift2 : (O.toricLift (p ^ n) hm).1 ≫ pullback.snd O.g Λ.σA = muStr ↥A O.toricRank (p ^ n) :=
    (O.toricLift (p ^ n) hm).2
  have hsec : Spec.map (CommRingCat.ofHom χA.toRingHom) ≫ muStr ↥A O.toricRank (p ^ n) = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom χA.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ↥A (muCoord ↥A O.toricRank (p ^ n)))) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : χA.toRingHom.comp (algebraMap ↥A (muCoord ↥A O.toricRank (p ^ n))) = RingHom.id ↥A := by
      rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]; rfl
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  have hs'g : s'1 ≫ O.g = Λ.σA := by
    simp only [s'1, Category.assoc]
    rw [pullback.condition, ← Category.assoc ((O.toricLift (p ^ n) hm).1), hlift2, ← Category.assoc, hsec,
      Category.id_comp]

  have hgen' : (O.pts x).1 = barPt A ≫ s'1 := by
    rw [← hχ, ModularCurve.JHNeronObjectAtP.toricPoint, Equiv.apply_symm_apply]
    show (RelativeGroupLaw.baseChangePointToBase Λ.σA
      (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank (p ^ n) χ) (O.toricLift (p ^ n) hm))).1 = _
    rw [RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe]
    show Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ (O.toricLift (p ^ n) hm).1 ≫ pullback.fst O.g Λ.σA = _
    rw [← N4Alg.subtype_comp_liftA A O.toricRank (p ^ n) hm χ, specMap_comp]
    rfl

  have hss' : s.1 = s'1 := by
    refine ext_of_isDominant_of_isSeparated O.g ?_ (barPt A) ?_
    · rw [s.2, hs'g]
    · rw [← hs, hgen']

  have hsκ1 : sκ.1 = Spec.map (CommRingCat.ofHom ((residue ↥A).comp χA.toRingHom)) ≫
      (O.toricLift (p ^ n) hm).1 ≫ pullback.fst O.g Λ.σA := by
    rw [hsκ, hss', specMap_comp]
    rfl
  rw [hχA, N4Alg.residue_comp_liftA_eq A O.toricRank (p ^ n) p n rfl χ] at hsκ1

  obtain ⟨hread, hmul, -⟩ :=
    ModularCurve.JHNeronObjectAtP.exists_nodeUnit_eq_residue_toricLift_and_mul_and_eq_one
      p M H hpM A hA Λ O (p ^ n) hm
  obtain ⟨wb, hwb⟩ := hread (N4Alg.triv A O.toricRank (p ^ n))
  have hwb2 := hmul (WithConv.toConv (N4Alg.triv A O.toricRank (p ^ n))) (WithConv.toConv (N4Alg.triv A O.toricRank (p ^ n)))
    wb wb hwb hwb
  rw [N4Alg.triv_convMul_triv A O.toricRank (p ^ n)] at hwb2

  have hnode : GluedPic0.nodeUnit O.ssFinset (wb + wb) = GluedPic0.nodeUnit O.ssFinset wb := by
    apply O.ptsSp.injective
    exact Subtype.ext (hwb2.symm.trans hwb)
  have hzero : GluedPic0.nodeUnit O.ssFinset wb = 0 := by
    have h := hnode
    rw [map_add] at h
    rw [← add_sub_cancel_right (GluedPic0.nodeUnit O.ssFinset wb) (GluedPic0.nodeUnit O.ssFinset wb), h, sub_self]

  have hfin : sκ = O.ptsSp 0 := by
    apply Subtype.ext
    rw [hsκ1, ← hzero, ← hwb]
  simp [hfin]

end

end S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_eq_zero_of_mem_toricPts_pow
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_eq_zero_of_mem_toricPts_pow (solution)
