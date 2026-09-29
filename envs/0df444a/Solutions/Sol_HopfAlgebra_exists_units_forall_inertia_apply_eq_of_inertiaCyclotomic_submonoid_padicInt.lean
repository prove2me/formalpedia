-- Prove2me | solution 1 for HopfAlgebra.exists_units_forall_inertia_apply_eq_of_inertiaCyclotomic_submonoid_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d70595ee-3616-520a-bdb2-c87ca4f011a6

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_GaloisRep_OrdinaryUnitClasses
import Theorems.Thm_KummerO_forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial_of_isAlgClosed
import Theorems.Thm_PadicAlgCl_exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq
import Theorems.Thm_HopfAlgebra_forall_withConv_pow_eq_one_of_forall_algHom_pow_eq_one_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_units_forall_inertia_apply_eq_of_inertiaCyclotomic_submonoid_padicInt
p2m_attr_erase "instance" "CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ExtCitation.LocalLevel.coe_smul_OO"

set_option autoImplicit false

open scoped NNReal TensorProduct

noncomputable section

namespace S17Asm

open WithConv

theorem exists_cycloExp (q : ℕ) [Fact q.Prime] {K L : Type*} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) : ∃ n : ℕ, ∀ ζ : L, ζ ^ q = 1 → σ ζ = ζ ^ n := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : IsCyclic ↥(rootsOfUnity q L) := rootsOfUnity.isCyclic L q
  let φ : ↥(rootsOfUnity q L) →* ↥(rootsOfUnity q L) := restrictRootsOfUnity (σ : L →+* L) q
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic φ
  have hq0 : (0 : ℤ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  refine ⟨(m % q).toNat, fun ζ hζ => ?_⟩
  let z : ↥(rootsOfUnity q L) := rootsOfUnity.mkOfPowEq ζ hζ
  have hz : ((z : Lˣ) : L) = ζ := rootsOfUnity.coe_mkOfPowEq hζ
  have hzq : z ^ (q : ℤ) = 1 := by
    rw [zpow_natCast]
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact (mem_rootsOfUnity q (z : Lˣ)).mp z.2
  have h1 : σ ζ = ((φ z : ↥(rootsOfUnity q L)) : Lˣ) := by
    rw [restrictRootsOfUnity_coe_apply, hz]; rfl
  have h2 : φ z = z ^ ((m % q).toNat : ℤ) := by
    rw [hm z, zpow_eq_zpow_emod m hzq, Int.toNat_of_nonneg (Int.emod_nonneg _ hq0.ne')]
  rw [h1, h2, zpow_natCast, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, hz]

section BaseChangePoints

variable {R S H T : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [Bialgebra R H]
  [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

def resPt (f : WithConv (S ⊗[R] H →ₐ[S] T)) : WithConv (H →ₐ[R] T) :=
  toConv (((ofConv f).restrictScalars R).comp (Algebra.TensorProduct.includeRight : H →ₐ[R] S ⊗[R] H))

omit [Bialgebra R H] in
theorem resPt_apply' [Algebra R H] (f : WithConv (S ⊗[R] H →ₐ[S] T)) (h : H) :
    ofConv (toConv (((ofConv f).restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : H →ₐ[R] S ⊗[R] H)) : WithConv (H →ₐ[R] T)) h =
      ofConv f ((1 : S) ⊗ₜ[R] h) := rfl

@[scoped simp] theorem resPt_apply (f : WithConv (S ⊗[R] H →ₐ[S] T)) (h : H) :
    ofConv (resPt f) h = ofConv f ((1 : S) ⊗ₜ[R] h) := rfl

theorem resPt_one : resPt (1 : WithConv (S ⊗[R] H →ₐ[S] T)) = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro h
  rw [resPt_apply, AlgHom.convOne_apply, AlgHom.convOne_apply, TensorProduct.counit_tmul,
    CommSemiring.counit_apply, Algebra.smul_def, mul_one, ← IsScalarTower.algebraMap_apply R S T]

theorem resPt_mul (f g : WithConv (S ⊗[R] H →ₐ[S] T)) : resPt (f * g) = resPt f * resPt g := by
  classical
  apply WithConv.ext
  apply AlgHom.ext
  intro h
  rw [resPt_apply, AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul,
    CommSemiring.comul_apply]
  let 𝓡 := Coalgebra.Repr.arbitrary R h
  rw [← 𝓡.eq]
  simp only [TensorProduct.tmul_sum, map_sum, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
    Algebra.TensorProduct.lift_tmul, resPt_apply]

theorem resPt_pow (f : WithConv (S ⊗[R] H →ₐ[S] T)) (n : ℕ) : resPt (f ^ n) = resPt f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, resPt_one]
  | succ n ih => rw [pow_succ, pow_succ, resPt_mul, ih]

def extPt (g : WithConv (H →ₐ[R] T)) : WithConv (S ⊗[R] H →ₐ[S] T) :=
  toConv (Algebra.TensorProduct.lift (Algebra.ofId S T) (ofConv g) (fun _ _ => Commute.all _ _))

theorem resPt_extPt (g : WithConv (H →ₐ[R] T)) : resPt (extPt (S := S) g) = g := by
  apply WithConv.ext
  apply AlgHom.ext
  intro h
  rw [resPt_apply, extPt, ofConv_toConv, Algebra.TensorProduct.lift_tmul, map_one, one_mul]

theorem resPt_injective : Function.Injective (resPt : WithConv (S ⊗[R] H →ₐ[S] T) → WithConv (H →ₐ[R] T)) := by
  intro f g hfg
  apply WithConv.ext
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · exact congrArg ofConv hfg

theorem extPt_resPt (f : WithConv (S ⊗[R] H →ₐ[S] T)) : extPt (resPt f) = f :=
  resPt_injective (resPt_extPt _)

theorem resPt_bijective :
    Function.Bijective (resPt : WithConv (S ⊗[R] H →ₐ[S] T) → WithConv (H →ₐ[R] T)) :=
  ⟨resPt_injective, fun g => ⟨extPt g, resPt_extPt g⟩⟩

def resPtHom : WithConv (S ⊗[R] H →ₐ[S] T) →* WithConv (H →ₐ[R] T) :=
  { toFun := resPt, map_one' := resPt_one, map_mul' := resPt_mul }

@[scoped simp] theorem resPtHom_apply (f : WithConv (S ⊗[R] H →ₐ[S] T)) : resPtHom f = resPt f := rfl

omit [Bialgebra R H] in

theorem forall_apply_eq_of_forall_tmul [Algebra R H] (τ : T →+* T) (hτ : ∀ s : S, τ (algebraMap S T s) = algebraMap S T s)
    (f g : S ⊗[R] H →ₐ[S] T) (hfg : ∀ h : H, g ((1 : S) ⊗ₜ[R] h) = τ (f ((1 : S) ⊗ₜ[R] h))) :
    ∀ b : S ⊗[R] H, g b = τ (f b) := by
  let τA : T →ₐ[S] T := { τ with commutes' := hτ }
  have hτA : ∀ x, τA x = τ x := fun _ => rfl
  have key : g = τA.comp f := by
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply AlgHom.ext
      intro h
      exact hfg h
  intro b
  rw [key]
  rfl

end BaseChangePoints

section PointsDict

variable {L : Type*} [Field L] {A : ValuationSubring L} {O : Type*} [CommRing O] [Algebra O ↥A]
  [Algebra O L] [IsScalarTower O ↥A L]
variable (B : Type*) [CommRing B] [Bialgebra O B]

omit [Bialgebra O B] in
theorem algebraMap_mem (x : O) : algebraMap O L x ∈ A := by
  rw [IsScalarTower.algebraMap_apply O ↥A L]
  exact (algebraMap O ↥A x).2

abbrev jA : ↥A →ₐ[O] L := IsScalarTower.toAlgHom O ↥A L

omit [Bialgebra O B] in
theorem jA_apply (a : ↥A) : jA (A := A) (O := O) a = (a : L) := rfl

omit [Bialgebra O B] in

theorem apply_mem_of_moduleFinite {B : Type*} [CommRing B] [Algebra O B] [Module.Finite O B]
    (f : B →ₐ[O] L) (h : B) : f h ∈ A := by
  classical
  have hOA : ∀ x : O, algebraMap O L x ∈ A := algebraMap_mem (A := A) (O := O)
  have hint : IsIntegral O (f h) := (Algebra.IsIntegral.isIntegral (R := O) h).map f
  obtain ⟨p, hpm, hpev⟩ := hint
  rw [← A.valuation_le_one_iff]
  by_contra hgt
  rw [not_le] at hgt
  have hy0 : A.valuation (f h) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hgt)
  have hsum : ∑ i ∈ Finset.range (p.natDegree + 1),
      algebraMap O L (p.coeff i) * f h ^ i = 0 := by
    rw [← Polynomial.eval₂_eq_sum_range]
    exact hpev
  rw [Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hsum
  have hyd : f h ^ p.natDegree
      = -∑ i ∈ Finset.range p.natDegree, algebraMap O L (p.coeff i) * f h ^ i :=
    eq_neg_of_add_eq_zero_right hsum
  have hlt : A.valuation (∑ i ∈ Finset.range p.natDegree, algebraMap O L (p.coeff i) * f h ^ i)
        < A.valuation (f h) ^ p.natDegree := by
    apply Valuation.map_sum_lt _ (pow_ne_zero _ hy0)
    intro i hi
    have hi' : i < p.natDegree := Finset.mem_range.mp hi
    rw [Valuation.map_mul, Valuation.map_pow]
    calc A.valuation (algebraMap O L (p.coeff i)) * A.valuation (f h) ^ i
        ≤ 1 * A.valuation (f h) ^ i := by
          apply mul_le_mul_left
          exact (A.valuation_le_one_iff _).mpr (hOA (p.coeff i))
      _ = A.valuation (f h) ^ i := one_mul _
      _ < A.valuation (f h) ^ p.natDegree := pow_lt_pow_right₀ hgt hi'
  have hcontra : A.valuation (f h ^ p.natDegree) < A.valuation (f h) ^ p.natDegree := by
    rw [hyd, Valuation.map_neg]
    exact hlt
  rw [Valuation.map_pow] at hcontra
  exact lt_irrefl _ hcontra

def toQ (f : WithConv (B →ₐ[O] ↥A)) : WithConv (B →ₐ[O] L) :=
  toConv ((jA (A := A) (O := O)).comp (ofConv f))

theorem toQ_apply (f : WithConv (B →ₐ[O] ↥A)) (b : B) :
    ofConv (toQ B f) b = ((ofConv f b : ↥A) : L) := rfl

theorem toQ_injective : Function.Injective (toQ (A := A) (O := O) B) := by
  intro f g hfg
  apply WithConv.ext
  apply AlgHom.ext
  intro b
  apply Subtype.ext
  have := congrArg (fun φ : WithConv (B →ₐ[O] L) => ofConv φ b) hfg
  exact this

theorem toQ_mul (f g : WithConv (B →ₐ[O] ↥A)) : toQ B (f * g) = toQ B f * toQ B g := by
  apply WithConv.ext
  show (jA (A := A) (O := O)).comp (ofConv (f * g)) = _
  rw [AlgHom.comp_convMul_distrib]
  rfl

theorem toQ_one : toQ (A := A) (O := O) B 1 = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro b
  rw [toQ_apply]
  show (((1 : WithConv (B →ₐ[O] ↥A)) b : ↥A) : L) = (1 : WithConv (B →ₐ[O] L)) b
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply, IsScalarTower.algebraMap_apply O ↥A L]
  rfl

def ofQ [Module.Finite O B] (φ : WithConv (B →ₐ[O] L)) : WithConv (B →ₐ[O] ↥A) :=
  toConv
    { toFun := fun b => ⟨ofConv φ b, apply_mem_of_moduleFinite (ofConv φ) b⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y)
      commutes' := fun r => Subtype.ext (by
        show ofConv φ (algebraMap O B r) = ((algebraMap O ↥A r : ↥A) : L)
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply O ↥A L]
        rfl) }

theorem toQ_ofQ [Module.Finite O B] (φ : WithConv (B →ₐ[O] L)) : toQ B (ofQ (A := A) B φ) = φ := by
  apply WithConv.ext; apply AlgHom.ext; intro b; rfl

theorem toQ_bijective [Module.Finite O B] : Function.Bijective (toQ (A := A) (O := O) B) :=
  ⟨toQ_injective B, fun φ => ⟨ofQ B φ, toQ_ofQ B φ⟩⟩

def toQHom : WithConv (B →ₐ[O] ↥A) →* WithConv (B →ₐ[O] L) :=
  { toFun := toQ (A := A) (O := O) B, map_one' := toQ_one B, map_mul' := toQ_mul B }

@[scoped simp] theorem toQHom_apply (f : WithConv (B →ₐ[O] ↥A)) : toQHom B f = toQ (A := A) (O := O) B f := rfl

end PointsDict

end S17Asm
p2m_reactivate "P2MW.S_HopfAlgebra_exists_units_forall_inertia_apply_eq_of_inertiaCyclotomic_submonoid_padicInt.S17Asm"

open S17Asm WithConv in

theorem S17Asm.core
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hirr : Irreducible (p : O))
    [Algebra ℤ_[p] O] [Algebra O (PadicAlgCl p)] [IsScalarTower ℤ_[p] O (PadicAlgCl p)]
    (hOA : ∀ x : O, algebraMap O (PadicAlgCl p) x ∈ padicIntegers p)
    (hOinj : Function.Injective (algebraMap O (PadicAlgCl p)))
    (hOfix : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ↔ ∀ x : O, σ (algebraMap O (PadicAlgCl p) x) = algebraMap O (PadicAlgCl p) x)
    (hOmax : ∀ y ∈ padicIntegers p,
      (∀ σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], σ y = y) → ∃ x : O, algebraMap O (PadicAlgCl p) x = y)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Flat ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H]
    (hHp : ∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), f ^ p = 1)
    (D : Submonoid (WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)))
    (hDcyc : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ c : ℕ, (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → σ ζ = ζ ^ c) →
        ∀ f ∈ D, ∀ g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          (∀ h : H, g h = σ (f h)) → g = f ^ c)
    (hquot : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
        (∀ h : H, g h = σ (f h)) → ∃ d ∈ D, g = f * d) :
    ∃ (t : ℕ) (u β : Fin t → PadicAlgCl p),
      (∀ i, ‖u i‖₊ = 1) ∧
      (∀ i, ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → σ (u i) = u i) ∧
      (∀ i, β i ^ p = u i) ∧
      ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → σ ζ = ζ) → (∀ i, σ (β i) = β i) →
          ∀ f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), (∀ h : H, g h = σ (f h)) → g = f := by
  classical
  have hpp : p.Prime := Fact.out

  let ι : O →+* ↥(padicIntegers p) :=
    RingHom.codRestrict (algebraMap O (PadicAlgCl p)) (padicIntegers p).toSubring hOA
  have hιcoe : ∀ x : O, ((ι x : ↥(padicIntegers p)) : PadicAlgCl p) = algebraMap O (PadicAlgCl p) x := fun _ => rfl
  letI algOA : Algebra O ↥(padicIntegers p) := ι.toAlgebra
  have hιalg : ∀ x : O, algebraMap O ↥(padicIntegers p) x = ι x := fun _ => rfl
  haveI : IsScalarTower O ↥(padicIntegers p) (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hιinj : Function.Injective ι := fun x y h => hOinj (by rw [← hιcoe, ← hιcoe, h])
  have hιfix : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ↔
      ∀ x : O, σ ((ι x : ↥(padicIntegers p)) : PadicAlgCl p) = ((ι x : ↥(padicIntegers p)) : PadicAlgCl p) :=
    fun σ => hOfix σ
  have hιmax : ∀ a : ↥(padicIntegers p), (∀ σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p],
      σ (a : PadicAlgCl p) = (a : PadicAlgCl p)) → a ∈ Set.range ι := by
    intro a ha
    obtain ⟨x, hx⟩ := hOmax (a : PadicAlgCl p) a.2 ha
    exact ⟨x, Subtype.ext hx⟩

  have hequiv : (Valued.v : Valuation (PadicAlgCl p) ℝ≥0).IsEquiv (padicIntegers p).valuation :=
    Valuation.isEquiv_valuation_valuationSubring _
  have hA : (padicIntegers p).LiesOverPrime p := by
    show ((p : ℕ) : PadicAlgCl p) ∈ (padicIntegers p).nonunits
    rw [ValuationSubring.mem_nonunits_iff, ← hequiv.lt_one_iff_lt_one, PadicAlgCl.valuation_p, one_div]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hpp.one_lt

  haveI : Module.Free ℤ_[p] H := Module.free_of_flat_of_isLocalRing

  let Ψ : WithConv (O ⊗[ℤ_[p]] H →ₐ[O] ↥(padicIntegers p)) →* WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) :=
    (resPtHom (R := ℤ_[p]) (S := O) (H := H) (T := PadicAlgCl p)).comp
      (toQHom (A := padicIntegers p) (O := O) (O ⊗[ℤ_[p]] H))
  have hΨ : ∀ f (h : H), Ψ f h = ((ofConv f ((1 : O) ⊗ₜ[ℤ_[p]] h) : ↥(padicIntegers p)) : PadicAlgCl p) :=
    fun _ _ => rfl
  have hΨbij : Function.Bijective Ψ :=
    (resPt_bijective (R := ℤ_[p]) (S := O) (H := H) (T := PadicAlgCl p)).comp
      (toQ_bijective (A := padicIntegers p) (O := O) (O ⊗[ℤ_[p]] H))

  have hrel : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ f g : WithConv (O ⊗[ℤ_[p]] H →ₐ[O] ↥(padicIntegers p)),
        (∀ b, ((ofConv g b : ↥(padicIntegers p)) : PadicAlgCl p) = σ ((ofConv f b : ↥(padicIntegers p)) : PadicAlgCl p)) ↔
          (∀ h : H, Ψ g h = σ (Ψ f h)) := by
    intro σ hσ f g
    constructor
    · intro hb h
      rw [hΨ, hΨ]
      exact hb _
    · intro hh
      have hfixO : ∀ s : O, (σ : PadicAlgCl p →+* PadicAlgCl p) (algebraMap O (PadicAlgCl p) s) =
          algebraMap O (PadicAlgCl p) s := fun s => (hOfix σ).mp hσ s
      have := forall_apply_eq_of_forall_tmul (R := ℤ_[p]) (S := O) (H := H) (T := PadicAlgCl p)
        (σ : PadicAlgCl p →+* PadicAlgCl p) hfixO (ofConv (toQ (O ⊗[ℤ_[p]] H) f)) (ofConv (toQ (O ⊗[ℤ_[p]] H) g))
        (fun h => hh h)
      intro b
      exact this b

  have hL : ∀ f : WithConv (O ⊗[ℤ_[p]] H →ₐ[O] PadicAlgCl p), f ^ p = 1 := by
    intro f
    apply resPt_injective (R := ℤ_[p]) (S := O) (H := H) (T := PadicAlgCl p)
    rw [resPt_pow, resPt_one]
    exact hHp _
  have hBq : ∀ (T : Type) [CommRing T] [Algebra O T] (f : WithConv (O ⊗[ℤ_[p]] H →ₐ[O] T)), f ^ p = 1 :=
    fun T _ _ f => HopfAlgebra.forall_withConv_pow_eq_one_of_forall_algHom_pow_eq_one_of_isAlgClosed O
      (O ⊗[ℤ_[p]] H) (PadicAlgCl p) hOinj p hL T f

  choose n hn using fun σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p => exists_cycloExp p σ

  let D' : Submonoid (WithConv (O ⊗[ℤ_[p]] H →ₐ[O] ↥(padicIntegers p))) := D.comap Ψ
  have hD'cyc : ∀ σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], ∀ f ∈ D',
      ∀ g : WithConv (O ⊗[ℤ_[p]] H →ₐ[O] ↥(padicIntegers p)),
      (∀ b, ((ofConv g b : ↥(padicIntegers p)) : PadicAlgCl p) = σ ((ofConv f b : ↥(padicIntegers p)) : PadicAlgCl p)) →
        g = f ^ n σ := by
    intro σ hσ f hf g hfg
    apply hΨbij.1
    rw [map_pow]
    exact hDcyc σ hσ (n σ) (hn σ) (Ψ f) (Submonoid.mem_comap.mp hf) (Ψ g) ((hrel σ hσ f g).mp hfg)
  have hD'quot : ∀ σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p],
      ∀ f g : WithConv (O ⊗[ℤ_[p]] H →ₐ[O] ↥(padicIntegers p)),
      (∀ b, ((ofConv g b : ↥(padicIntegers p)) : PadicAlgCl p) = σ ((ofConv f b : ↥(padicIntegers p)) : PadicAlgCl p)) →
        ∃ d ∈ D', g = f * d := by
    intro σ hσ f g hfg
    obtain ⟨d, hd, hgd⟩ := hquot σ hσ (Ψ f) (Ψ g) ((hrel σ hσ f g).mp hfg)
    obtain ⟨d', rfl⟩ := hΨbij.2 d
    refine ⟨d', Submonoid.mem_comap.mpr hd, hΨbij.1 ?_⟩
    rw [map_mul, hgd]

  obtain ⟨t, u, β, hu1, hufix, hβ, hfix⟩ :=
    KummerO.forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial_of_isAlgClosed p hp2
      (padicIntegers p) hA O hirr ι hιinj hιalg hιfix hιmax (O ⊗[ℤ_[p]] H) hBq n hn D' hD'cyc hD'quot
  refine ⟨t, u, β, fun i => ?_, hufix, hβ, ?_⟩
  ·
    have := hu1 i
    rw [← hequiv.eq_one_iff_eq_one] at this
    exact this
  · intro σ hσ hμ hβσ f g hfg
    obtain ⟨f', rfl⟩ := hΨbij.2 f
    obtain ⟨g', rfl⟩ := hΨbij.2 g
    rw [hfix σ hσ hμ hβσ f' g' ((hrel σ hσ f' g').mpr hfg)]

open S17Asm in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Flat ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H]
    (hHp : ∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), f ^ p = 1)
    (D : Submonoid (WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)))
    (hDcyc : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ c : ℕ, (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → σ ζ = ζ ^ c) →
        ∀ f ∈ D, ∀ g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          (∀ h : H, g h = σ (f h)) → g = f ^ c)
    (hquot : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
        (∀ h : H, g h = σ (f h)) → ∃ d ∈ D, g = f * d) :
    ∃ (t : ℕ) (u β : Fin t → PadicAlgCl p),
      (∀ i, ‖u i‖₊ = 1) ∧
      (∀ i, ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → σ (u i) = u i) ∧
      (∀ i, β i ^ p = u i) ∧
      ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → σ ζ = ζ) → (∀ i, σ (β i) = β i) →
          ∀ f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), (∀ h : H, g h = σ (f h)) → g = f := by
  classical

  obtain ⟨Osub, hOsubA, hZpO, hOdvr, hOirr, -, hOfix, hOmax⟩ :=
    PadicAlgCl.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq p
  haveI : IsDiscreteValuationRing ↥Osub := hOdvr
  letI : Algebra ℤ_[p] ↥Osub := (RingHom.codRestrict (algebraMap ℤ_[p] (PadicAlgCl p)) Osub hZpO).toAlgebra
  haveI : IsScalarTower ℤ_[p] ↥Osub (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact S17Asm.core p hp2 ↥Osub hOirr (fun x => hOsubA x.2) Subtype.val_injective
    (fun σ => (hOfix σ).trans ⟨fun h x => h x.1 x.2, fun h x hx => h ⟨x, hx⟩⟩)
    (fun y hy hfix => ⟨⟨y, hOmax y hy hfix⟩, rfl⟩) H hHp D hDcyc hquot

end
end S_HopfAlgebra_exists_units_forall_inertia_apply_eq_of_inertiaCyclotomic_submonoid_padicInt
end P2MW
export P2MW.S_HopfAlgebra_exists_units_forall_inertia_apply_eq_of_inertiaCyclotomic_submonoid_padicInt (solution)
