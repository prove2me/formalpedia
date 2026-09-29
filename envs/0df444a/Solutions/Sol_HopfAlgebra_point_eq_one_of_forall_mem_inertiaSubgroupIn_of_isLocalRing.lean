-- Prove2me | solution 1 for HopfAlgebra.point_eq_one_of_forall_mem_inertiaSubgroupIn_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/83b78549-6a3a-5d63-a782-938a0e2b4c38

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq
import Theorems.Thm_HopfAlgebra_point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal
import Theorems.Thm_GaloisRep_natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf
import Theorems.Thm_HopfAlgebra_isUnit_withConv_algHom
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_of_isLocalRing
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false

noncomputable section

namespace DichA1Proof

open GaloisRep TensorProduct

variable {p : ℕ}

private def galB (p : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    AlgebraicClosure ℚ →ₐ[ratLocalizedAt p] AlgebraicClosure ℚ :=
  { σ.toRingEquiv.toRingHom with
    commutes' := fun r => by
      change σ (algebraMap (ratLocalizedAt p) (AlgebraicClosure ℚ) r) = _
      rw [IsScalarTower.algebraMap_apply (ratLocalizedAt p) ℚ (AlgebraicClosure ℚ)]
      exact σ.commutes _ }

@[scoped simp] private theorem galB_apply (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : AlgebraicClosure ℚ) :
    galB p σ x = σ x := rfl

section Values

variable {H : Type} [CommRing H] [HopfAlgebra (ratLocalizedAt p) H]

private theorem apply_fixed (P : ValuationSubring (AlgebraicClosure ℚ))
    (f : WithConv (H →ₐ[ratLocalizedAt p] AlgebraicClosure ℚ))
    (hf : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ g : WithConv (H →ₐ[ratLocalizedAt p] AlgebraicClosure ℚ),
      (∀ h : H, g h = σ (f h)) → g = f)
    (h : H) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    σ (f h) = f h := by
  have hg := hf σ hσ (WithConv.toConv ((galB p σ).comp f.ofConv)) (fun _ => rfl)
  exact (congrArg (fun k : WithConv (H →ₐ[ratLocalizedAt p] AlgebraicClosure ℚ) => k h) hg :)

variable [Module.Finite (ratLocalizedAt p) H]

private theorem apply_mem (P : ValuationSubring (AlgebraicClosure ℚ))
    (hRp : ∀ r : ratLocalizedAt p, algebraMap (ratLocalizedAt p) (AlgebraicClosure ℚ) r ∈ P)
    (f : H →ₐ[ratLocalizedAt p] AlgebraicClosure ℚ) (h : H) : f h ∈ P := by
  let ιP : ratLocalizedAt p →+* P := (algebraMap (ratLocalizedAt p) (AlgebraicClosure ℚ)).codRestrict P.toSubring hRp
  have hcomp : (algebraMap P (AlgebraicClosure ℚ)).comp ιP = algebraMap (ratLocalizedAt p) (AlgebraicClosure ℚ) :=
    RingHom.ext fun _ => rfl
  obtain ⟨q, hqm, hq⟩ : IsIntegral (ratLocalizedAt p) (f h) := (Algebra.IsIntegral.isIntegral h).map f
  have hintP : IsIntegral P (f h) :=
    ⟨q.map ιP, hqm.map ιP, by rw [Polynomial.eval₂_map, hcomp]; exact hq⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintP
  rw [← hy]
  exact y.2

end Values

section Congruence

variable [Fact p.Prime] {H : Type} [CommRing H] [HopfAlgebra (ratLocalizedAt p) H]

private theorem comap_isMaximal {I : Ideal H} [I.IsPrime] (hpI : (algebraMap (ratLocalizedAt p) H p) ∈ I) :
    (I.comap (algebraMap (ratLocalizedAt p) H)).IsMaximal := by
  haveI : IsLocalRing (ratLocalizedAt p) := GaloisRep.ratLocalizedAt.isLocalRing Fact.out
  haveI : IsDiscreteValuationRing (ratLocalizedAt p) :=
    GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  have hmax : IsLocalRing.maximalIdeal (ratLocalizedAt p) = Ideal.span {((p : ℕ) : ratLocalizedAt p)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp
      (GaloisRep.irreducible_natCast_ratLocalizedAt p Fact.out)
  have hle : IsLocalRing.maximalIdeal (ratLocalizedAt p) ≤ I.comap (algebraMap (ratLocalizedAt p) H) := by
    rw [hmax, Ideal.span_le, Set.singleton_subset_iff]
    simpa using hpI
  have hne : I.comap (algebraMap (ratLocalizedAt p) H) ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  rw [← (IsLocalRing.maximalIdeal.isMaximal (ratLocalizedAt p)).eq_of_le hne hle]
  exact IsLocalRing.maximalIdeal.isMaximal _

variable [Module.Finite (ratLocalizedAt p) H] [IsLocalRing H]

private theorem ker_eq_maximalIdeal {K : Type*} [CommRing K] [IsDomain K] (φ : H →+* K)
    (hp : φ (algebraMap (ratLocalizedAt p) H p) = 0) : RingHom.ker φ = IsLocalRing.maximalIdeal H := by
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hmax : (RingHom.ker φ).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ratLocalizedAt p) (RingHom.ker φ)
      (comap_isMaximal (by simpa [RingHom.mem_ker] using hp))
  exact IsLocalRing.eq_maximalIdeal hmax

private theorem valuation_sub_counit_lt_one (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (hRp : ∀ r : ratLocalizedAt p, algebraMap (ratLocalizedAt p) (AlgebraicClosure ℚ) r ∈ P)
    (f : H →ₐ[ratLocalizedAt p] AlgebraicClosure ℚ) (hfP : ∀ h : H, f h ∈ P) (h : H) :
    P.valuation (f h - algebraMap (ratLocalizedAt p) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1 := by

  let fP : H →+* P := (f : H →+* AlgebraicClosure ℚ).codRestrict P.toSubring hfP
  let ιP : ratLocalizedAt p →+* P := (algebraMap (ratLocalizedAt p) (AlgebraicClosure ℚ)).codRestrict P.toSubring hRp
  let εP : H →+* P := ιP.comp (Bialgebra.counitAlgHom (ratLocalizedAt p) H).toRingHom
  let φ₁ : H →+* IsLocalRing.ResidueField P := (IsLocalRing.residue P).comp fP
  let φ₂ : H →+* IsLocalRing.ResidueField P := (IsLocalRing.residue P).comp εP

  have hpP : ((p : ℕ) : P) ∈ IsLocalRing.maximalIdeal P := by
    rw [ValuationSubring.valuation_lt_one_iff, ← ValuationSubring.mem_nonunits_iff]
    simp at hP ⊢
    exact hP
  have hιp : ιP p = (p : P) := Subtype.ext (by simp [ιP])
  have hfp : fP (algebraMap (ratLocalizedAt p) H p) = (p : P) := Subtype.ext (by simp [fP])
  have h1 : φ₁ (algebraMap (ratLocalizedAt p) H p) = 0 := by
    simp only [φ₁, RingHom.comp_apply, hfp]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hpP
  have hεalg : ∀ r : ratLocalizedAt p, εP (algebraMap (ratLocalizedAt p) H r) = ιP r := by
    intro r
    simp only [εP, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Bialgebra.counitAlgHom_apply,
      Bialgebra.counit_algebraMap]
  have h2 : φ₂ (algebraMap (ratLocalizedAt p) H p) = 0 := by
    simp only [φ₂, RingHom.comp_apply, hεalg, hιp]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hpP

  have hk : RingHom.ker φ₁ = RingHom.ker φ₂ := (ker_eq_maximalIdeal φ₁ h1).trans (ker_eq_maximalIdeal φ₂ h2).symm

  have hmem : h - algebraMap (ratLocalizedAt p) H (Coalgebra.counit h) ∈ RingHom.ker φ₁ := by
    rw [hk, RingHom.mem_ker, map_sub, sub_eq_zero]
    simp only [φ₂, RingHom.comp_apply, hεalg]
    simp only [εP, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Bialgebra.counitAlgHom_apply]
  rw [RingHom.mem_ker] at hmem
  change IsLocalRing.residue P (fP (h - algebraMap (ratLocalizedAt p) H (Coalgebra.counit h))) = 0 at hmem
  rw [IsLocalRing.residue_eq_zero_iff, map_sub, ValuationSubring.valuation_lt_one_iff] at hmem
  have hval : ((fP h - fP (algebraMap (ratLocalizedAt p) H (Coalgebra.counit h)) : P) : AlgebraicClosure ℚ) =
      f h - algebraMap (ratLocalizedAt p) (AlgebraicClosure ℚ) (Coalgebra.counit h) := by
    simp [fP]
  rw [← hval]
  exact hmem

end Congruence

section Kill

variable [Fact p.Prime] {H : Type} [CommRing H] [HopfAlgebra (ratLocalizedAt p) H] [Module.Finite (ratLocalizedAt p) H]
  [Module.Flat (ratLocalizedAt p) H] [Coalgebra.IsCocomm (ratLocalizedAt p) H]

private theorem eq_one_of_values (hp2 : p ≠ 2) (hH : 0 < Module.finrank (ratLocalizedAt p) H)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (O : Subring (AlgebraicClosure ℚ))
    [IsDiscreteValuationRing O] (hirr : Irreducible ((p : ℕ) : O))
    (hdom : ∀ x : O, P.valuation (x : AlgebraicClosure ℚ) < 1 → ¬ IsUnit x)
    (hRp : ∀ r : ratLocalizedAt p, algebraMap (ratLocalizedAt p) (AlgebraicClosure ℚ) r ∈ O)
    (f : WithConv (H →ₐ[ratLocalizedAt p] AlgebraicClosure ℚ)) (hfO : ∀ h : H, f h ∈ O)
    (hcong : ∀ h : H,
      P.valuation (f h - algebraMap (ratLocalizedAt p) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1) :
    f = 1 := by
  classical

  letI algO : Algebra (ratLocalizedAt p) O :=
    ((algebraMap (ratLocalizedAt p) (AlgebraicClosure ℚ)).codRestrict O hRp).toAlgebra
  have halgO : ∀ r : ratLocalizedAt p, ((algebraMap (ratLocalizedAt p) O r : O) : AlgebraicClosure ℚ) =
      algebraMap (ratLocalizedAt p) (AlgebraicClosure ℚ) r := fun _ => rfl

  let fO : H →ₐ[ratLocalizedAt p] O :=
    { (f.ofConv : H →+* AlgebraicClosure ℚ).codRestrict O hfO with
      commutes' := fun r => Subtype.ext (by simp [halgO]) }
  have hfO_apply : ∀ h : H, ((fO h : O) : AlgebraicClosure ℚ) = f h := fun _ => rfl

  have hcomm : ∀ (a : O) (b : H), Commute ((AlgHom.id O O) a) (fO b) := fun _ _ => Commute.all _ _
  let x : WithConv (O ⊗[ratLocalizedAt p] H →ₐ[O] O) :=
    WithConv.toConv (Algebra.TensorProduct.lift (AlgHom.id O O) fO hcomm)
  have hx_tmul : ∀ (o : O) (h : H), x (o ⊗ₜ[ratLocalizedAt p] h) = o * fO h := fun o h => by
    change Algebra.TensorProduct.lift (AlgHom.id O O) fO hcomm (o ⊗ₜ[ratLocalizedAt p] h) = _
    rw [Algebra.TensorProduct.lift_tmul]
    rfl

  have hunitO : ∀ h : H, fO h - algebraMap (ratLocalizedAt p) O (Coalgebra.counit h) ∈ IsLocalRing.maximalIdeal O := by
    intro h
    apply (IsLocalRing.mem_maximalIdeal _).mpr
    apply hdom
    change P.valuation ((fO h : AlgebraicClosure ℚ) -
      ((algebraMap (ratLocalizedAt p) O (Coalgebra.counit h) : O) : AlgebraicClosure ℚ)) < 1
    rw [hfO_apply, halgO]
    exact hcong h
  have hx1 : ∀ h' : O ⊗[ratLocalizedAt p] H,
      x h' - algebraMap O O (Coalgebra.counit h') ∈ IsLocalRing.maximalIdeal O := by
    intro h'
    induction h' using TensorProduct.induction_on with
    | zero => simp
    | tmul o h =>
      rw [hx_tmul, TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.algebraMap_self,
        RingHom.id_apply, Algebra.smul_def, mul_comm (algebraMap _ O _) o, ← mul_sub]
      exact Ideal.mul_mem_left _ o (hunitO h)
    | add a b ha hb =>
      have := Ideal.add_mem _ ha hb
      simp only [map_add] at this ⊢
      convert this using 1
      ring

  let oInc : O →ₐ[ratLocalizedAt p] AlgebraicClosure ℚ := { O.subtype with commutes' := fun _ => rfl }
  let Φ : WithConv (O ⊗[ratLocalizedAt p] H →ₐ[O] O) → WithConv (H →ₐ[ratLocalizedAt p] AlgebraicClosure ℚ) :=
    fun y => WithConv.toConv (oInc.comp ((y.ofConv.restrictScalars (ratLocalizedAt p)).comp
      Algebra.TensorProduct.includeRight))
  have hΦ : Function.Injective Φ := by
    intro y₁ y₂ hy
    have hpt : ∀ h : H, y₁ (1 ⊗ₜ[ratLocalizedAt p] h) = y₂ (1 ⊗ₜ[ratLocalizedAt p] h) := by
      intro h
      have := congrArg (fun k : WithConv (H →ₐ[ratLocalizedAt p] AlgebraicClosure ℚ) => k h) hy
      exact Subtype.ext this
    refine WithConv.ext (Algebra.TensorProduct.ext' fun o h => ?_)
    have ho : o ⊗ₜ[ratLocalizedAt p] h = o • ((1 : O) ⊗ₜ[ratLocalizedAt p] h) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    change y₁.ofConv (o ⊗ₜ h) = y₂.ofConv (o ⊗ₜ h)
    rw [ho, map_smul, map_smul]
    exact congrArg _ (hpt h)
  haveI : Finite (WithConv (H →ₐ[ratLocalizedAt p] AlgebraicClosure ℚ)) := by
    apply Nat.finite_of_card_ne_zero
    rw [GaloisRep.natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf p H]
    exact hH.ne'
  haveI : Finite (WithConv (O ⊗[ratLocalizedAt p] H →ₐ[O] O)) := Finite.of_injective Φ hΦ

  obtain ⟨u, hu⟩ := HopfAlgebra.isUnit_withConv_algHom x
  have hfin : IsOfFinOrder u := isOfFinOrder_of_finite u
  have hn : 0 < orderOf u := hfin.orderOf_pos
  have hxn : x ^ orderOf u = 1 := by
    rw [← hu, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]

  have hx : x = 1 :=
    HopfAlgebra.point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal O p hp2 hirr
      (O ⊗[ratLocalizedAt p] H) x hx1 (orderOf u) hn hxn

  refine WithConv.ext (AlgHom.ext fun h => ?_)
  have h1 : x ((1 : O) ⊗ₜ[ratLocalizedAt p] h) = fO h := by rw [hx_tmul, one_mul]
  rw [hx] at h1
  change (1 : WithConv (O ⊗[ratLocalizedAt p] H →ₐ[O] O)).ofConv ((1 : O) ⊗ₜ[ratLocalizedAt p] h) = fO h at h1
  rw [AlgHom.convOne_apply, TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Algebra.smul_def, mul_one] at h1
  change f.ofConv h = (1 : WithConv (H →ₐ[ratLocalizedAt p] AlgebraicClosure ℚ)).ofConv h
  rw [AlgHom.convOne_apply, ← hfO_apply, ← h1, halgO]

end Kill

private theorem point_eq_one
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H] [IsLocalRing H]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ))
    (hf : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g = f) :
    f = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩

  obtain ⟨O, hOP, hRpO, hdvr, hirr, hdom, -, hfixO⟩ :=
    ValuationSubring.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq p P hP
  haveI := hdvr
  have hRp : ∀ r : ratLocalizedAt p, algebraMap (ratLocalizedAt p) (AlgebraicClosure ℚ) r ∈ O := by
    intro r
    rw [IsScalarTower.algebraMap_apply (ratLocalizedAt p) ℚ (AlgebraicClosure ℚ)]
    exact hRpO r r.2
  have hRpP : ∀ r : ratLocalizedAt p, algebraMap (ratLocalizedAt p) (AlgebraicClosure ℚ) r ∈ P :=
    fun r => hOP (hRp r)

  have hfP : ∀ h : H, f h ∈ P := apply_mem P hRpP f.ofConv
  have hfO : ∀ h : H, f h ∈ O := fun h => hfixO (f h) (hfP h) (fun σ hσ => apply_fixed P f hf h σ hσ)

  haveI : IsLocalRing (ratLocalizedAt p) := GaloisRep.ratLocalizedAt.isLocalRing Fact.out
  haveI : Module.Free (ratLocalizedAt p) H := Module.free_of_flat_of_isLocalRing
  have hH : 0 < Module.finrank (ratLocalizedAt p) H := Module.finrank_pos
  exact eq_one_of_values hp2 hH P O hirr hdom hRp f hfO
    (fun h => valuation_sub_counit_lt_one P hP hRpP f.ofConv hfP h)

end DichA1Proof
p2m_reactivate "P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_of_isLocalRing.DichA1Proof"

end
p2m_reactivate "P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_of_isLocalRing.DichA1Proof"

theorem solution
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H] [IsLocalRing H]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ))
    (hf : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g = f) :
    f = 1 := by
  exact DichA1Proof.point_eq_one hp hp2 H P hP f hf

end S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_of_isLocalRing
end P2MW
export P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_of_isLocalRing (solution)
