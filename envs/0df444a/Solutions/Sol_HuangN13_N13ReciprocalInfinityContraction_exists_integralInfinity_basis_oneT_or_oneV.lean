-- Prove2me | solution 1 for HuangN13.N13ReciprocalInfinityContraction.exists_integralInfinity_basis_oneT_or_oneV
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:21:22.135671+00:00
-- url     : https://prove2.me/submissions/1171def6-0ebe-47be-b4ff-e507c624df31

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore

set_option autoImplicit false

section
section
set_option autoImplicit false
open scoped TensorProduct
open Module
namespace MazurProof.N13FiniteFlatBasisLift
noncomputable section
universe uR uB
variable {R : Type uR} {B : Type uB}
variable [CommRing R] [IsLocalRing R]
variable [CommRing B] [Algebra R B]
variable [Module.Finite R B] [Module.Flat R B]
local notation "k" => IsLocalRing.ResidueField R
/--
If `{1,x}` becomes a supplied basis after residue-field base change, then
the same literal family is a basis over the local ring.
-/
theorem exists_basis_oneX
    (x : B)
    (b₀ : Basis (Fin 2) k (k ⊗[R] B))
    (hb₀ : ∀ i : Fin 2,
      TensorProduct.mk R k B 1 (oneX x i) = b₀ i) :
    ∃ b : Basis (Fin 2) R B,
      (b : Fin 2 → B) = oneX x := by
  have hfamily :
      (TensorProduct.mk R k B 1 ∘ oneX x) =
        (b₀ : Fin 2 → k ⊗[R] B) := by
    funext i
    exact hb₀ i
  have hk :
      Function.Bijective
        (Finsupp.linearCombination k
          (TensorProduct.mk R k B 1 ∘ oneX x)) := by
    rw [hfamily]
    exact
      ⟨b₀.linearIndependent,
        fun y => ⟨b₀.repr y, b₀.linearCombination_repr y⟩⟩
  have hR :
      Function.Bijective
        (Finsupp.linearCombination R (oneX x)) :=
    Module.IsLocalRing.linearCombination_bijective_of_flat
      (R := R) (M := B) (oneX x) hk
  have hspan :
      ⊤ ≤ Submodule.span R (Set.range (oneX x)) := by
    rw [← Finsupp.range_linearCombination]
    exact (LinearMap.range_eq_top.mpr hR.2).ge
  refine ⟨Basis.mk hR.1 hspan, ?_⟩
  exact Basis.coe_mk hR.1 hspan
end
end MazurProof.N13FiniteFlatBasisLift
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GeneralizedMumfordReduction
noncomputable section
@[simp] theorem reduceBase_two :
    reduceBase (2 : R₂) = 0 := by
  rw [← RingHom.mem_ker, reduceBase, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p]
  exact Ideal.subset_span (by simp)
end
end MazurProof.N13GeneralizedMumfordReduction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13QuotientReduction
noncomputable section
universe uA uS
variable {A : Type uA} {S : Type uS}
variable [CommRing A] [CommRing S]
/-- Surjectivity descends to the quotient rings. -/
theorem inducedQuotientMap_surjective
    (f : A →+* S)
    (hf : Function.Surjective f)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J) :
    Function.Surjective
      (inducedQuotientMap f I J hmap) := by
  unfold inducedQuotientMap
  apply Ideal.Quotient.lift_surjective_of_surjective
  exact Ideal.Quotient.mk_surjective.comp hf
end
end MazurProof.N13QuotientReduction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13QuotientReduction
noncomputable section
universe uA uS
variable {A : Type uA} {S : Type uS}
variable [CommRing A] [CommRing S]
/-- For a surjective ambient map, the quotient kernel is the image of the
ambient kernel. -/
theorem ker_inducedQuotientMap_eq_map_ker
    (f : A →+* S)
    (hf : Function.Surjective f)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J) :
    RingHom.ker (inducedQuotientMap f I J hmap) =
      Ideal.map (Ideal.Quotient.mk I) (RingHom.ker f) := by
  have hkerComp :
      RingHom.ker ((Ideal.Quotient.mk J).comp f) =
        I ⊔ RingHom.ker f := by
    calc
      RingHom.ker ((Ideal.Quotient.mk J).comp f) =
          Ideal.comap f
            (RingHom.ker (Ideal.Quotient.mk J)) :=
        (RingHom.comap_ker (Ideal.Quotient.mk J) f).symm
      _ = Ideal.comap f J := by
        rw [Ideal.mk_ker]
      _ = Ideal.comap f (Ideal.map f I) :=
        congrArg (Ideal.comap f) hmap.symm
      _ = I ⊔ Ideal.comap f (⊥ : Ideal S) :=
        Ideal.comap_map_of_surjective f hf I
      _ = I ⊔ RingHom.ker f := by
        rfl
  unfold inducedQuotientMap
  rw [Ideal.ker_quotient_lift, hkerComp,
    Ideal.map_sup, Ideal.map_quotient_self]
  simp
end
end MazurProof.N13QuotientReduction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13QuotientReduction
noncomputable section
universe uA uS
variable {A : Type uA} {S : Type uS}
variable [CommRing A] [CommRing S]
/-- A principal ambient kernel remains principal after quotienting. -/
theorem ker_inducedQuotientMap_eq_span
    (f : A →+* S)
    (hf : Function.Surjective f)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J)
    (r : A)
    (hker :
      RingHom.ker f = Ideal.span ({r} : Set A)) :
    RingHom.ker (inducedQuotientMap f I J hmap) =
      Ideal.span
        ({Ideal.Quotient.mk I r} : Set (A ⧸ I)) := by
  rw [ker_inducedQuotientMap_eq_map_ker
      f hf I J hmap,
    hker, Ideal.map_span]
  simp
end
end MazurProof.N13QuotientReduction
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.SexticMumfordQuotientBasis
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : SexticMumford.Model K)
variable (D : SexticMumford.SemiMumford M)
theorem residueBasis_apply
    (hdeg : D.u.natDegree = 2) (i : Fin 2) :
    residueBasis M D hdeg i =
      AdjoinRoot.root D.u ^ (i : ℕ) := by
  change
    ((AdjoinRoot.powerBasis' D.u_monic).basis.reindex
        (finCongr hdeg)) i =
      AdjoinRoot.root D.u ^ (i : ℕ)
  rw [Basis.reindex_apply, PowerBasis.basis_eq_pow,
    AdjoinRoot.powerBasis'_gen]
  rfl
end
end MazurProof.SexticMumfordQuotientBasis
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.SexticMumfordQuotientBasis
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : SexticMumford.Model K)
variable (D : SexticMumford.SemiMumford M)
@[simp] theorem residueBasis_zero
    (hdeg : D.u.natDegree = 2) :
    residueBasis M D hdeg (0 : Fin 2) = 1 := by
  simp [residueBasis_apply]
end
end MazurProof.SexticMumfordQuotientBasis
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.SexticMumfordQuotientBasis
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : SexticMumford.Model K)
variable (D : SexticMumford.SemiMumford M)
@[simp] theorem residueBasis_one
    (hdeg : D.u.natDegree = 2) :
    residueBasis M D hdeg (1 : Fin 2) =
      AdjoinRoot.root D.u := by
  simp [residueBasis_apply]
end
end MazurProof.SexticMumfordQuotientBasis
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.SexticMumfordQuotientBasis
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : SexticMumford.Model K)
variable (D : SexticMumford.SemiMumford M)
@[simp] theorem quotientBasis_zero
    (hdeg : D.u.natDegree = 2) :
    quotientBasis M D hdeg (0 : Fin 2) = 1 := by
  change
    (SexticMumford.mumfordQuotientAlgEquiv M D).symm
        (residueBasis M D hdeg 0) = 1
  rw [residueBasis_zero]
  exact map_one (SexticMumford.mumfordQuotientAlgEquiv M D).symm
end
end MazurProof.SexticMumfordQuotientBasis
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.SexticMumfordQuotientBasis
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : SexticMumford.Model K)
variable (D : SexticMumford.SemiMumford M)
set_option backward.isDefEq.respectTransparency.types false in
@[simp] theorem quotientBasis_one
    (hdeg : D.u.natDegree = 2) :
    quotientBasis M D hdeg (1 : Fin 2) =
      Ideal.Quotient.mk
        (SexticMumford.mumfordIdeal M D.u D.v)
        (SexticMumford.xClass M X) := by
  change
    (SexticMumford.mumfordQuotientAlgEquiv M D).symm
        (residueBasis M D hdeg 1) =
      Ideal.Quotient.mk
        (SexticMumford.mumfordIdeal M D.u D.v)
        (SexticMumford.xClass M X)
  rw [residueBasis_one]
  apply (SexticMumford.mumfordQuotientAlgEquiv M D).injective
  rw [(SexticMumford.mumfordQuotientAlgEquiv M D).apply_symm_apply]
  simp only [SexticMumford.mumfordQuotientAlgEquiv]
  change
    AdjoinRoot.root D.u =
      SexticMumford.mumfordEval M D
        (SexticMumford.xClass M X)
  rw [SexticMumford.mumfordEval_xClass]
  rfl
end
end MazurProof.SexticMumfordQuotientBasis
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13QuotientVerticalFlatness
noncomputable section
universe uR uA
variable {R : Type uR} {A : Type uA}
variable [CommRing R] [IsDomain R]
variable [CommRing A] [Algebra R A]
/--
An ideal saturated with respect to every nonzero base scalar has a
torsion-free quotient over the base.
-/
theorem quotient_isTorsionFree_of_scalar_saturated
    (I : Ideal A)
    (hsaturated :
      ∀ (r : R), r ≠ 0 →
        ∀ a : A, algebraMap R A r * a ∈ I → a ∈ I) :
    Module.IsTorsionFree R (A ⧸ I) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r z hrz
  by_cases hr : r = 0
  · exact Or.inl hr
  · right
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply hsaturated r hr a
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul]
    change
      algebraMap R (A ⧸ I) r *
          Ideal.Quotient.mk I a = 0
    simpa only [Algebra.smul_def] using hrz
end
end MazurProof.N13QuotientVerticalFlatness
end
end

section
section
set_option autoImplicit false
open scoped TensorProduct
open Module
namespace MazurProof.N13TensorSpecialFiber
noncomputable section
universe uR uk uB uC uι
variable {R : Type uR} {k : Type uk}
variable {B : Type uB} {C : Type uC}
variable [CommRing R] [CommRing k]
variable [CommRing B] [CommRing C]
variable [Algebra R k] [Algebra R B] [Algebra R C]
variable [Algebra k C] [IsScalarTower R k C]
@[simp] theorem tensorLinearEquiv_tmul
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (hq : Function.Surjective (algebraMap R k))
    (π : R)
    (hπ : algebraMap R k π = 0)
    (hg : Function.Surjective g)
    (hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R B π} : Set B))
    (a : k) (b : B) :
    tensorLinearEquiv g hfactor hq π hπ hg hker
        (a ⊗ₜ[R] b) =
      a • g b := by
  exact tensorLinearMap_tmul g hfactor a b
end
end MazurProof.N13TensorSpecialFiber
end
end

section
section
set_option autoImplicit false
open scoped TensorProduct
open Module
namespace MazurProof.N13TensorSpecialFiber
noncomputable section
universe uR uk uB uC uι
variable {R : Type uR} {k : Type uk}
variable {B : Type uB} {C : Type uC}
variable [CommRing R] [CommRing k]
variable [CommRing B] [CommRing C]
variable [Algebra R k] [Algebra R B] [Algebra R C]
variable [Algebra k C] [IsScalarTower R k C]
section ResidueField
variable [IsLocalRing R]
local notation "κ" => IsLocalRing.ResidueField R
variable [Algebra (IsLocalRing.ResidueField R) C]
variable [IsScalarTower R (IsLocalRing.ResidueField R) C]
@[simp] theorem residueLinearEquiv_tmul
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap κ C).comp (IsLocalRing.residue R))
    (π : R)
    (hπ : π ∈ IsLocalRing.maximalIdeal R)
    (hg : Function.Surjective g)
    (hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R B π} : Set B))
    (a : κ) (b : B) :
    residueLinearEquiv g hfactor π hπ hg hker
        (a ⊗ₜ[R] b) =
      a • g b := by
  exact
    tensorLinearEquiv_tmul
      (g := g)
      (hfactor := residueFactor g hfactor)
      (hq := residueAlgebraMap_surjective (R := R))
      (π := π)
      (hπ := residueElement_eq_zero π hπ)
      (hg := hg)
      (hker := hker)
      a b
end ResidueField
end
end MazurProof.N13TensorSpecialFiber
end
end

section
section
set_option autoImplicit false
open scoped TensorProduct
open Module
namespace MazurProof.N13TensorSpecialFiber
noncomputable section
universe uR uk uB uC uι
variable {R : Type uR} {k : Type uk}
variable {B : Type uB} {C : Type uC}
variable [CommRing R] [CommRing k]
variable [CommRing B] [CommRing C]
variable [Algebra R k] [Algebra R B] [Algebra R C]
variable [Algebra k C] [IsScalarTower R k C]
section BasisTransport
variable {ι : Type uι}
theorem mk_eq_pullbackBasis
    (e : k ⊗[R] B ≃ₗ[k] C)
    (v : ι → B)
    (bC : Basis ι k C)
    (heval :
      ∀ i : ι,
        e (TensorProduct.mk R k B 1 (v i)) = bC i) :
    ∀ i : ι,
      TensorProduct.mk R k B 1 (v i) =
        pullbackBasis e bC i := by
  intro i
  apply e.injective
  simpa [pullbackBasis] using heval i
end BasisTransport
end
end MazurProof.N13TensorSpecialFiber
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.N13TwoGeneratorFiberBasis
noncomputable section
universe uK uB
variable {K : Type uK} {B : Type uB}
variable [Field K] [CommRing B] [Algebra K B] [Nontrivial B]
/-- If a two-dimensional algebra is generated by `x` and `y`, then one of
`{1,x}` and `{1,y}` is linearly independent. -/
theorem oneX_or_oneY_linearIndependent
    (x y : B)
    (hfinrank : Module.finrank K B = 2)
    (hgen : Algebra.adjoin K ({x, y} : Set B) = ⊤) :
    LinearIndependent K ![1, x] ∨
      LinearIndependent K ![1, y] := by
  by_contra h
  have hxNot : ¬ LinearIndependent K ![1, x] :=
    fun hx ↦ h (Or.inl hx)
  have hyNot : ¬ LinearIndependent K ![1, y] :=
    fun hy ↦ h (Or.inr hy)
  have hx :
      ∃ a : K, algebraMap K B a = x := by
    rw [LinearIndependent.pair_iff'
      (one_ne_zero : (1 : B) ≠ 0)] at hxNot
    push Not at hxNot
    obtain ⟨a, ha⟩ := hxNot
    exact ⟨a, by simpa [Algebra.smul_def] using ha⟩
  have hy :
      ∃ b : K, algebraMap K B b = y := by
    rw [LinearIndependent.pair_iff'
      (one_ne_zero : (1 : B) ≠ 0)] at hyNot
    push Not at hyNot
    obtain ⟨b, hb⟩ := hyNot
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hbot : (⊥ : Subalgebra K B) = ⊤ := by
    apply top_unique
    rw [← hgen, Algebra.adjoin_le_iff]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> simp
  have hsurj : Function.Surjective (algebraMap K B) := by
    intro z
    have hz : z ∈ (⊥ : Subalgebra K B) := by
      rw [hbot]
      trivial
    simpa only [Algebra.mem_bot, Set.mem_range] using hz
  have hbij :
      Function.Bijective (algebraMap K B) :=
    ⟨FaithfulSMul.algebraMap_injective K B, hsurj⟩
  have hrank :
      Module.finrank K B = 1 :=
    Module.finrank_of_bijective_algebraMap hbij
  omega
end
end MazurProof.N13TwoGeneratorFiberBasis
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.N13TwoGeneratorFiberBasis
noncomputable section
universe uK uB
variable {K : Type uK} {B : Type uB}
variable [Field K] [CommRing B] [Algebra K B] [Nontrivial B]
/-- Basis-valued form of `oneX_or_oneY_linearIndependent`. -/
theorem exists_basis_oneX_or_oneY
    (x y : B)
    (hfinrank : Module.finrank K B = 2)
    (hgen : Algebra.adjoin K ({x, y} : Set B) = ⊤) :
    (∃ b : Basis (Fin 2) K B, (b : Fin 2 → B) = ![1, x]) ∨
      (∃ b : Basis (Fin 2) K B, (b : Fin 2 → B) = ![1, y]) := by
  rcases oneX_or_oneY_linearIndependent x y hfinrank hgen with hx | hy
  · left
    let b : Basis (Fin 2) K B :=
      basisOfLinearIndependentOfCardEqFinrank hx (by simp [hfinrank])
    exact ⟨b, by simp [b]⟩
  · right
    let b : Basis (Fin 2) K B :=
      basisOfLinearIndependentOfCardEqFinrank hy (by simp [hfinrank])
    exact ⟨b, by simp [b]⟩
end
end MazurProof.N13TwoGeneratorFiberBasis
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
open scoped TensorProduct
namespace MazurProof.N13ContractQuotientXYBasis
noncomputable section
universe uF uK uA uι
theorem exists_basis_restrictScalars_of_surjective
    {F : Type uF} {K : Type uK} {A : Type uA} {ι : Type uι}
    [Field F] [Field K] [CommRing A]
    [Algebra F K] [Algebra F A] [Algebra K A]
    [IsScalarTower F K A] [Fintype ι]
    (hFK : Function.Surjective (algebraMap F K))
    (b : Basis ι K A) :
    ∃ bF : Basis ι F A, (bF : ι → A) = b := by
  have hli :
      LinearIndependent F (b : ι → A) :=
    b.linearIndependent.restrict_scalars' F
  have hspan :
      ⊤ ≤ Submodule.span F (Set.range (b : ι → A)) := by
    intro z _
    rw [← b.sum_repr z]
    apply Submodule.sum_mem
    intro i _
    obtain ⟨a, ha⟩ := hFK (b.repr z i)
    rw [← ha, IsScalarTower.algebraMap_smul K]
    exact
      Submodule.smul_mem _ a
        (Submodule.subset_span (Set.mem_range_self i))
  let bF : Basis ι F A :=
    Basis.mk hli hspan
  exact ⟨bF, Basis.coe_mk hli hspan⟩
end
end MazurProof.N13ContractQuotientXYBasis
end
end

section
section
set_option autoImplicit false
open Module
namespace MazurProof.N13TwoFiberNoEscape
noncomputable section
universe uR uk uB uC
variable {R : Type uR} {k : Type uk}
variable {B : Type uB} {C : Type uC}
variable [CommRing R] [IsDomain R]
variable [Field k]
variable [CommRing B] [CommRing C]
variable [Algebra R k] [Algebra R B] [Algebra R C]
variable [Algebra k C] [IsScalarTower R k C]
variable [Module.IsTorsionFree R B]
section FractionFieldClearing
universe uK uG
variable {K : Type uK} {G : Type uG}
variable [Field K] [CommRing G]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra R G] [Algebra K G]
variable [IsScalarTower R K G]
/--
An injective generic-fibre map carrying the pair to a basis proves
integral linear independence of the same pair.
-/
theorem pair_linearIndependent_of_fraction_basis
    (q : B →+* G)
    (hfactor :
      q.comp (algebraMap R B) = algebraMap R G)
    (hq : Function.Injective q)
    (e₀ e₁ : B)
    (bG : Basis (Fin 2) K G)
    (he₀ : q e₀ = bG 0)
    (he₁ : q e₁ = bG 1) :
    LinearIndependent R (pairFamily e₀ e₁) := by
  let qAlg : B →ₐ[R] G :=
    { toRingHom := q
      commutes' := fun a => by
        change q (algebraMap R B a) = algebraMap R G a
        simpa only [RingHom.comp_apply] using
          DFunLike.congr_fun hfactor a }
  have hmap :
      qAlg.toLinearMap ∘ pairFamily e₀ e₁ =
        (bG : Fin 2 → G) := by
    funext i
    fin_cases i
    · exact he₀
    · exact he₁
  have hliMap :
      LinearIndependent R
        (qAlg.toLinearMap ∘ pairFamily e₀ e₁) := by
    rw [hmap]
    exact bG.linearIndependent.restrict_scalars' R
  exact
    (qAlg.toLinearMap.linearIndependent_iff
      (LinearMap.ker_eq_bot.mpr hq)).mp hliMap
end FractionFieldClearing
end
end MazurProof.N13TwoFiberNoEscape
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem infinityCurvePoly_natDegree :
    infinityCurvePoly.natDegree = 2 := by
  unfold infinityCurvePoly
  compute_degree <;> norm_num
end
end MazurProof.N13IntegralInfinityChart
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem reduceBase_two :
    reduceBase (2 : R₂) = 0 := by
  exact N13GeneralizedMumfordReduction.reduceBase_two
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem integral_curve_degree :
    N13IntegralInfinityChart.infinityCurvePoly.degree = 2 := by
  rw [degree_eq_natDegree
      N13IntegralInfinityChart.infinityCurvePoly_monic.ne_zero,
    N13IntegralInfinityChart.infinityCurvePoly_natDegree]
  norm_num
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
private theorem special_curve_degree :
    N13SpecialInfinityChart.curvePoly.degree = 2 := by
  rw [degree_eq_natDegree
      N13SpecialInfinityChart.curvePoly_monic.ne_zero,
    N13SpecialInfinityChart.curvePoly_natDegree]
  norm_num
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem integralNormalPoly_eq (z : IntegralRing) :
    integralNormalPoly z =
      C (integralCoeff0 z) + C (integralCoeffV z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ N13IntegralInfinityChart.infinityCurvePoly =
        C ((g %ₘ N13IntegralInfinityChart.infinityCurvePoly).coeff 0) +
          C ((g %ₘ N13IntegralInfinityChart.infinityCurvePoly).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := N13IntegralInfinityChart.infinityCurvePoly)
        N13IntegralInfinityChart.infinityCurvePoly_monic
        (n := 2) (by rw [integral_curve_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
theorem specialNormalPoly_eq (z : SpecialRing) :
    specialNormalPoly z =
      C (specialCoeff0 z) + C (specialCoeffV z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ N13SpecialInfinityChart.curvePoly =
        C ((g %ₘ N13SpecialInfinityChart.curvePoly).coeff 0) +
          C ((g %ₘ N13SpecialInfinityChart.curvePoly).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := N13SpecialInfinityChart.curvePoly)
        N13SpecialInfinityChart.curvePoly_monic
        (n := 2) (by rw [special_curve_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Every ordinary element has a unique rank-two expression. -/
theorem integral_recompose (z : IntegralRing) :
    integralBaseClass (integralCoeff0 z) +
        integralBaseClass (integralCoeffV z) *
          N13IntegralInfinityChart.vClass = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        integralBaseClass (integralCoeff0 (AdjoinRoot.mk _ g)) +
              integralBaseClass (integralCoeffV (AdjoinRoot.mk _ g)) *
                N13IntegralInfinityChart.vClass =
            AdjoinRoot.mk _
              (C (integralCoeff0 (AdjoinRoot.mk _ g)) +
                C (integralCoeffV (AdjoinRoot.mk _ g)) * X) := by
                  simp only [integralBaseClass,
                    N13IntegralInfinityChart.vClass, map_add, map_mul,
                    AdjoinRoot.algebraMap_eq, AdjoinRoot.mk_C,
                    AdjoinRoot.mk_X]
        _ = AdjoinRoot.mk _ (integralNormalPoly (AdjoinRoot.mk _ g)) := by
              rw [integralNormalPoly_eq]
        _ = AdjoinRoot.mk _ g :=
          AdjoinRoot.mk_leftInverse
            N13IntegralInfinityChart.infinityCurvePoly_monic
            (AdjoinRoot.mk _ g)
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
/-- Every special element has a unique rank-two expression. -/
theorem special_recompose (z : SpecialRing) :
    specialBaseClass (specialCoeff0 z) +
        specialBaseClass (specialCoeffV z) *
          N13SpecialInfinityChart.vClass = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        specialBaseClass (specialCoeff0 (AdjoinRoot.mk _ g)) +
              specialBaseClass (specialCoeffV (AdjoinRoot.mk _ g)) *
                N13SpecialInfinityChart.vClass =
            AdjoinRoot.mk _
              (C (specialCoeff0 (AdjoinRoot.mk _ g)) +
                C (specialCoeffV (AdjoinRoot.mk _ g)) * X) := by
                  simp only [specialBaseClass,
                    N13SpecialInfinityChart.vClass, map_add, map_mul,
                    AdjoinRoot.algebraMap_eq, AdjoinRoot.mk_C,
                    AdjoinRoot.mk_X]
        _ = AdjoinRoot.mk _ (specialNormalPoly (AdjoinRoot.mk _ g)) := by
              rw [specialNormalPoly_eq]
        _ = AdjoinRoot.mk _ g :=
          AdjoinRoot.mk_leftInverse
            N13SpecialInfinityChart.curvePoly_monic
            (AdjoinRoot.mk _ g)
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem specialCoeff0_baseClass (p : SpecialBase) :
    specialCoeff0 (specialBaseClass p) = p := by
  change
    (C p %ₘ N13SpecialInfinityChart.curvePoly).coeff 0 = p
  rw [(modByMonic_eq_self_iff
      N13SpecialInfinityChart.curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [special_curve_degree]
      norm_num)
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem specialCoeffV_baseClass (p : SpecialBase) :
    specialCoeffV (specialBaseClass p) = 0 := by
  change
    (C p %ₘ N13SpecialInfinityChart.curvePoly).coeff 1 = 0
  rw [(modByMonic_eq_self_iff
      N13SpecialInfinityChart.curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [special_curve_degree]
      norm_num)
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem specialCoeff0_vClass :
    specialCoeff0 N13SpecialInfinityChart.vClass = 0 := by
  change (X %ₘ N13SpecialInfinityChart.curvePoly).coeff 0 = 0
  rw [(modByMonic_eq_self_iff
      N13SpecialInfinityChart.curvePoly_monic).mpr]
  · simp
  · rw [degree_X, special_curve_degree]
    norm_num
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem specialCoeffV_vClass :
    specialCoeffV N13SpecialInfinityChart.vClass = 1 := by
  change (X %ₘ N13SpecialInfinityChart.curvePoly).coeff 1 = 1
  rw [(modByMonic_eq_self_iff
      N13SpecialInfinityChart.curvePoly_monic).mpr]
  · simp
  · rw [degree_X, special_curve_degree]
    norm_num
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem specialCoeff0_baseClass_mul_vClass
    (p : SpecialBase) :
    specialCoeff0
        (specialBaseClass p * N13SpecialInfinityChart.vClass) = 0 := by
  change specialCoeff0
    ((algebraMap SpecialBase SpecialRing p) *
      N13SpecialInfinityChart.vClass) = 0
  rw [← Algebra.smul_def]
  simp
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem specialCoeffV_baseClass_mul_vClass
    (p : SpecialBase) :
    specialCoeffV
        (specialBaseClass p * N13SpecialInfinityChart.vClass) = p := by
  change specialCoeffV
    ((algebraMap SpecialBase SpecialRing p) *
      N13SpecialInfinityChart.vClass) = p
  rw [← Algebra.smul_def]
  simp
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
/-- Reduction is coefficientwise in the rank-two bases. -/
@[simp] theorem reduce_integralCoeff0 (z : IntegralRing) :
    specialCoeff0 (reduceCoordinate z) =
      reducePoly (integralCoeff0 z) := by
  calc
    specialCoeff0 (reduceCoordinate z) =
        specialCoeff0
          (reduceCoordinate
            (integralBaseClass (integralCoeff0 z) +
              integralBaseClass (integralCoeffV z) *
                N13IntegralInfinityChart.vClass)) := by
          rw [integral_recompose]
    _ = reducePoly (integralCoeff0 z) := by
      simp
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem reduce_integralCoeffV (z : IntegralRing) :
    specialCoeffV (reduceCoordinate z) =
      reducePoly (integralCoeffV z) := by
  calc
    specialCoeffV (reduceCoordinate z) =
        specialCoeffV
          (reduceCoordinate
            (integralBaseClass (integralCoeff0 z) +
              integralBaseClass (integralCoeffV z) *
                N13IntegralInfinityChart.vClass)) := by
          rw [integral_recompose]
    _ = reducePoly (integralCoeffV z) := by
      simp
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
/-- Coefficientwise reduction on the base polynomial ring is onto. -/
theorem reducePoly_surjective :
    Function.Surjective reducePoly :=
  Polynomial.map_surjective
    reduceBase
    (ZMod.ringHom_surjective PadicInt.toZMod)
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
/-- The ordinary infinity chart reduces onto its special fibre. -/
theorem reduceCoordinate_surjective :
    Function.Surjective reduceCoordinate := by
  intro z
  obtain ⟨p, hp⟩ :=
    reducePoly_surjective (specialCoeff0 z)
  obtain ⟨q, hq⟩ :=
    reducePoly_surjective (specialCoeffV z)
  refine ⟨
    integralBaseClass p +
      integralBaseClass q * N13IntegralInfinityChart.vClass,
    ?_⟩
  simp only [map_add, map_mul, reduce_integralBaseClass,
    reduce_vClass, hp, hq]
  exact special_recompose z
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
private theorem exists_eq_C_two_mul_of_reducePoly_eq_zero
    (p : IntegralBase) (hp : reducePoly p = 0) :
    ∃ q : IntegralBase, p = C (2 : R₂) * q := by
  have hmem : p ∈ RingHom.ker reducePoly :=
    RingHom.mem_ker.mpr hp
  rw [reducePoly, Polynomial.ker_mapRingHom, reduceBase,
    N13GeneralizedMumfordReduction.reduceBase,
    PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at hmem
  exact hmem
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
/-- Reduction has exactly the vertical principal ideal `(2)` as kernel. -/
theorem ker_reduceCoordinate :
    RingHom.ker reduceCoordinate =
      Ideal.span
        ({algebraMap R₂ IntegralRing (2 : R₂)} :
          Set IntegralRing) := by
  apply le_antisymm
  · intro z hz
    have hz0 : reduceCoordinate z = 0 :=
      RingHom.mem_ker.mp hz
    have h0 :
        reducePoly (integralCoeff0 z) = 0 := by
      rw [← reduce_integralCoeff0 z, hz0]
      simp
    have hV :
        reducePoly (integralCoeffV z) = 0 := by
      rw [← reduce_integralCoeffV z, hz0]
      simp
    obtain ⟨p, hp⟩ :=
      exists_eq_C_two_mul_of_reducePoly_eq_zero _ h0
    obtain ⟨q, hq⟩ :=
      exists_eq_C_two_mul_of_reducePoly_eq_zero _ hV
    rw [Ideal.mem_span_singleton]
    refine ⟨
      integralBaseClass p +
        integralBaseClass q * N13IntegralInfinityChart.vClass,
      ?_⟩
    rw [← integral_recompose z, hp, hq]
    calc
      integralBaseClass (C 2 * p) +
            integralBaseClass (C 2 * q) *
              N13IntegralInfinityChart.vClass =
          integralBaseClass (C 2) *
            (integralBaseClass p +
                integralBaseClass q *
                  N13IntegralInfinityChart.vClass) := by
            simp only [integralBaseClass, map_mul, mul_add]
            ring
      _ = algebraMap R₂ IntegralRing (2 : R₂) *
            (integralBaseClass p +
              integralBaseClass q *
                N13IntegralInfinityChart.vClass) := rfl
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change
      algebraMap R₂ IntegralRing (2 : R₂) ∈
        RingHom.ker reduceCoordinate
    rw [RingHom.mem_ker]
    change reduceCoordinate (integralBaseClass (C (2 : R₂))) = 0
    rw [reduce_integralBaseClass]
    simp [reducePoly, specialBaseClass]
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem xbar_eq_linear_tbar
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    xbar D =
      algebraMap Q₂ (GenericQuotient D) (-D.u.coeff 0) *
          tbar D -
        algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1) := by
  have hu :
      algebraMap Q₂ (GenericQuotient D) (D.u.coeff 0) *
          algebraMap Q₂ (GenericQuotient D) ((D.u.coeff 0)⁻¹) =
        1 := by
    rw [← map_mul]
    simp [h0]
  dsimp only [tbar]
  rw [map_neg, map_neg]
  calc
    xbar D =
        (algebraMap Q₂ (GenericQuotient D) (D.u.coeff 0) *
            algebraMap Q₂ (GenericQuotient D)
              ((D.u.coeff 0)⁻¹)) *
          (xbar D +
            algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1)) -
          algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1) := by
            rw [hu]
            ring
    _ =
        (-algebraMap Q₂ (GenericQuotient D) (D.u.coeff 0)) *
            (-algebraMap Q₂ (GenericQuotient D)
                ((D.u.coeff 0)⁻¹) *
              (xbar D +
                algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1))) -
          algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1) := by
            ring
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem infinityCurve_root
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    N13IntegralInfinityChart.infinityCurvePoly.eval₂
        (baseToGenericQuotient D) (vbar D) = 0 := by
  simp only [N13IntegralInfinityChart.infinityCurvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    eval₂_mul, sub_eq_zero]
  simpa [baseToGenericQuotient, coefficientToGenericQuotient,
    N13IntegralInfinityChart.hBase,
    N13IntegralInfinityChart.rhsBase] using
      vbar_relation D hdeg h0
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem integralInfinityToGenericQuotient_tClass
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    integralInfinityToGenericQuotient D hdeg h0
        N13IntegralInfinityChart.tClass = tbar D := by
  simp [integralInfinityToGenericQuotient,
    N13IntegralInfinityChart.tClass, baseToGenericQuotient]
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
def genericQuotientMap
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    InfinityRing ⧸ integralInfinityIdeal D hdeg h0 →+*
      GenericQuotient D :=
  Ideal.Quotient.lift
    (integralInfinityIdeal D hdeg h0)
    (integralInfinityToGenericQuotient D hdeg h0)
    (by
      intro a ha
      exact ha)
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem genericQuotientMap_mk
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (z : InfinityRing) :
    genericQuotientMap D hdeg h0
        (Ideal.Quotient.mk
          (integralInfinityIdeal D hdeg h0) z) =
      integralInfinityToGenericQuotient D hdeg h0 z :=
  Ideal.Quotient.lift_mk _ _ _
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem genericQuotientMap_injective
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    Function.Injective (genericQuotientMap D hdeg h0) := by
  intro z w hzw
  apply sub_eq_zero.mp
  obtain ⟨a, ha⟩ :=
    Ideal.Quotient.mk_surjective (z - w)
  rw [← ha]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change integralInfinityToGenericQuotient D hdeg h0 a = 0
  calc
    integralInfinityToGenericQuotient D hdeg h0 a =
        genericQuotientMap D hdeg h0
          (Ideal.Quotient.mk
            (integralInfinityIdeal D hdeg h0) a) :=
      (genericQuotientMap_mk D hdeg h0 a).symm
    _ = genericQuotientMap D hdeg h0 (z - w) :=
      congrArg (genericQuotientMap D hdeg h0) ha
    _ = 0 := by rw [map_sub, hzw, sub_self]
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem integralInfinityToGenericQuotient_xClass
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (p : R₂[X]) :
    integralInfinityToGenericQuotient D hdeg h0
        (N13IntegralInfinityGraphJacobian.xClassHom p) =
      baseToGenericQuotient D p := by
  change
    integralInfinityToGenericQuotient D hdeg h0
        (AdjoinRoot.of
          N13IntegralInfinityChart.infinityCurvePoly p) = _
  exact AdjoinRoot.lift_of (infinityCurve_root D hdeg h0)
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem integralInfinityToGenericQuotient_algebraMap
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (r : R₂) :
    integralInfinityToGenericQuotient D hdeg h0
        (algebraMap R₂ InfinityRing r) =
      algebraMap Q₂ (GenericQuotient D)
        (N13TwoAdicCoordinateBaseChange.coeffMap r) := by
  change
    integralInfinityToGenericQuotient D hdeg h0
        (N13IntegralInfinityGraphJacobian.xClassHom (C r)) = _
  rw [integralInfinityToGenericQuotient_xClass]
  simp [baseToGenericQuotient, coefficientToGenericQuotient]
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem integralInfinityIdeal_scalarSaturated
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    ∀ (r : R₂), r ≠ 0 → ∀ z : InfinityRing,
      algebraMap R₂ InfinityRing r * z ∈
          integralInfinityIdeal D hdeg h0 →
        z ∈ integralInfinityIdeal D hdeg h0 := by
  intro r hr z hz
  rw [integralInfinityIdeal, RingHom.mem_ker] at hz ⊢
  rw [map_mul, integralInfinityToGenericQuotient_algebraMap] at hz
  have hrQ :
      N13TwoAdicCoordinateBaseChange.coeffMap r ≠ 0 := by
    exact
      (IsFractionRing.injective R₂ Q₂).ne hr
  have hsunit :
      IsUnit
        (algebraMap Q₂ (GenericQuotient D)
          (N13TwoAdicCoordinateBaseChange.coeffMap r)) :=
    (isUnit_iff_ne_zero.mpr hrQ).map
      (algebraMap Q₂ (GenericQuotient D))
  let u : (GenericQuotient D)ˣ :=
    hsunit.unit
  have hu :
      (u : GenericQuotient D) =
        algebraMap Q₂ (GenericQuotient D)
          (N13TwoAdicCoordinateBaseChange.coeffMap r) :=
    hsunit.unit_spec
  calc
    integralInfinityToGenericQuotient D hdeg h0 z =
        ((u⁻¹ : (GenericQuotient D)ˣ) : GenericQuotient D) *
          ((u : GenericQuotient D) *
            integralInfinityToGenericQuotient D hdeg h0 z) := by
              simp
    _ = 0 := by rw [hu, hz, mul_zero]
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem integralInfinityQuotient_isTorsionFree
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    Module.IsTorsionFree R₂
      (InfinityRing ⧸ integralInfinityIdeal D hdeg h0) :=
  N13QuotientVerticalFlatness.quotient_isTorsionFree_of_scalar_saturated
      (integralInfinityIdeal D hdeg h0)
      (integralInfinityIdeal_scalarSaturated D hdeg h0)
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem integralInfinityQuotient_flat
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    Module.Flat R₂
      (InfinityRing ⧸ integralInfinityIdeal D hdeg h0) := by
  letI :
      Module.IsTorsionFree R₂
        (InfinityRing ⧸ integralInfinityIdeal D hdeg h0) :=
    integralInfinityQuotient_isTorsionFree D hdeg h0
  infer_instance
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem exists_genericQuotient_basis_oneT
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    ∃ bT : Basis (Fin 2) Q₂ (GenericQuotient D),
      (bT : Fin 2 → GenericQuotient D) =
        N13FiniteFlatBasisLift.oneX (tbar D) := by
  let bX :=
    SexticMumfordQuotientBasis.quotientBasis
      Model D.toSemi hdeg
  have hbX :
      (bX : Fin 2 → GenericQuotient D) =
        N13FiniteFlatBasisLift.oneX (xbar D) := by
    funext i
    fin_cases i
    · change bX (0 : Fin 2) = 1
      exact
        SexticMumfordQuotientBasis.quotientBasis_zero
          Model D.toSemi hdeg
    · change
        bX (1 : Fin 2) =
          Ideal.Quotient.mk
            (SexticMumford.mumfordIdeal
              Model D.toSemi.u D.toSemi.v)
            (SexticMumford.xClass Model X)
      exact
        SexticMumfordQuotientBasis.quotientBasis_one
          Model D.toSemi hdeg
  have hone : (1 : GenericQuotient D) ≠ 0 := by
    have hbX0 :
        bX (0 : Fin 2) = 1 :=
      SexticMumfordQuotientBasis.quotientBasis_zero
        Model D.toSemi hdeg
    intro h
    exact bX.ne_zero 0 (hbX0.trans h)
  have hliX :
      LinearIndependent Q₂
        (N13FiniteFlatBasisLift.oneX (xbar D)) := by
    rw [← hbX]
    exact bX.linearIndependent
  have hliT :
      LinearIndependent Q₂
        (N13FiniteFlatBasisLift.oneX (tbar D)) := by
    rw [show N13FiniteFlatBasisLift.oneX (tbar D) =
        ![1, tbar D] by rfl,
      LinearIndependent.pair_iff' hone]
    intro α hα
    have hxscalar :
        algebraMap Q₂ (GenericQuotient D)
            (-D.u.coeff 0 * α - D.u.coeff 1) =
          xbar D := by
      rw [xbar_eq_linear_tbar D hdeg h0, ← hα]
      simp only [map_sub, map_mul, map_neg, Algebra.smul_def,
        mul_one]
    have hnon :=
      (LinearIndependent.pair_iff' hone).mp
        (by
          simpa [N13FiniteFlatBasisLift.oneX] using hliX)
    exact
      hnon (-D.u.coeff 0 * α - D.u.coeff 1)
        (by simpa [Algebra.smul_def] using hxscalar)
  have hfin :
      Module.finrank Q₂ (GenericQuotient D) = 2 := by
    exact Module.finrank_eq_card_basis bX
  let bT : Basis (Fin 2) Q₂ (GenericQuotient D) :=
    basisOfLinearIndependentOfCardEqFinrank
      hliT (by simp [hfin])
  exact ⟨bT, by simp [bT]⟩
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
def genericQuotientAlgHom
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    (InfinityRing ⧸ integralInfinityIdeal D hdeg h0) →ₐ[R₂]
      GenericQuotient D where
  toRingHom := genericQuotientMap D hdeg h0
  commutes' r := by
    change
      integralInfinityToGenericQuotient D hdeg h0
          (algebraMap R₂ InfinityRing r) =
        algebraMap Q₂ (GenericQuotient D)
          (N13TwoAdicCoordinateBaseChange.coeffMap r)
    exact integralInfinityToGenericQuotient_algebraMap D hdeg h0 r
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem integralInfinityQuotient_finrank_eq_two
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (hfinite :
      Module.Finite R₂
        (InfinityRing ⧸ integralInfinityIdeal D hdeg h0)) :
    Module.finrank R₂
        (InfinityRing ⧸ integralInfinityIdeal D hdeg h0) =
      2 := by
  let Iinf := integralInfinityIdeal D hdeg h0
  let B := InfinityRing ⧸ Iinf
  let G := GenericQuotient D
  let q : B →+* G := genericQuotientMap D hdeg h0
  let qAlg : B →ₐ[R₂] G :=
    genericQuotientAlgHom D hdeg h0
  change Module.finrank R₂ B = 2
  letI : Module.Finite R₂ B := hfinite
  letI : Module.Flat R₂ B :=
    integralInfinityQuotient_flat D hdeg h0
  letI : Module.Free R₂ B :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨bT, hbT⟩ :=
    exists_genericQuotient_basis_oneT D hdeg h0
  letI : Module.Finite Q₂ G :=
    Module.Finite.of_basis bT
  have hq : Function.Injective q :=
    genericQuotientMap_injective D hdeg h0
  have hfactor :
      q.comp (algebraMap R₂ B) = algebraMap R₂ G := by
    ext r
    change
      integralInfinityToGenericQuotient D hdeg h0
          (algebraMap R₂ InfinityRing r) =
        algebraMap Q₂ (GenericQuotient D)
          (N13TwoAdicCoordinateBaseChange.coeffMap r)
    exact integralInfinityToGenericQuotient_algebraMap D hdeg h0 r
  have hli :
      LinearIndependent R₂
        (N13TwoFiberNoEscape.pairFamily
          (1 : B)
          (Ideal.Quotient.mk Iinf
            N13IntegralInfinityChart.tClass)) := by
    apply
      N13TwoFiberNoEscape.pair_linearIndependent_of_fraction_basis
        (R := R₂) (K := Q₂)
        q hfactor hq
        1
        (Ideal.Quotient.mk Iinf
          N13IntegralInfinityChart.tClass)
        bT
    · simpa [q, hbT, N13FiniteFlatBasisLift.oneX]
    · change
        genericQuotientMap D hdeg h0
            (Ideal.Quotient.mk
              (integralInfinityIdeal D hdeg h0)
              N13IntegralInfinityChart.tClass) =
          bT 1
      rw [genericQuotientMap_mk,
        integralInfinityToGenericQuotient_tClass]
      simpa [N13FiniteFlatBasisLift.oneX] using
        (congrFun hbT (1 : Fin 2)).symm
  have hlo : 2 ≤ Module.finrank R₂ B := by
    simpa using hli.fintype_card_le_finrank
  have hrank :
      Module.rank Q₂ G = Module.rank R₂ G :=
    IsLocalization.rank_eq Q₂ (nonZeroDivisors R₂) le_rfl
  have hGfinite : Module.rank R₂ G < Cardinal.aleph0 := by
    rw [← hrank]
    exact Module.rank_lt_aleph0 Q₂ G
  have hhi : Module.finrank R₂ B ≤ Module.finrank R₂ G :=
    Module.finrank_le_finrank_of_rank_le_rank
      (LinearMap.lift_rank_le_of_injective
        qAlg.toLinearMap hq)
      hGfinite
  have hfield :
      Module.finrank Q₂ G = Module.finrank R₂ G := by
    simpa only [Module.finrank] using
      congrArg Cardinal.toNat hrank
  have hGtwo : Module.finrank R₂ G = 2 := by
    rw [← hfield, Module.finrank_eq_card_basis bT]
    rfl
  rw [hGtwo] at hhi
  omega
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13ReciprocalInfinityContraction.instFactPrimeOfNatNat_fLT
private theorem specialInfinity_coordinate_adjoin_eq_top :
    Algebra.adjoin k
        ({N13SpecialInfinityChart.tClass,
          N13SpecialInfinityChart.vClass} : Set SpecialRing) =
      ⊤ := by
  let S : Subalgebra k SpecialRing :=
    Algebra.adjoin k
      ({N13SpecialInfinityChart.tClass,
        N13SpecialInfinityChart.vClass} : Set SpecialRing)
  have hbase (p : k[X]) :
      algebraMap k[X] SpecialRing p ∈ S := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [map_add]
        exact S.add_mem hp hq
    | monomial n a =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
        exact
          S.mul_mem (S.algebraMap_mem a)
            (S.pow_mem
              (Algebra.subset_adjoin
                (Set.mem_insert
                  N13SpecialInfinityChart.tClass
                  {N13SpecialInfinityChart.vClass})) n)
  apply Algebra.eq_top_iff.2
  intro z
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  change AdjoinRoot.mk N13SpecialInfinityChart.curvePoly p ∈ S
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      exact
        S.mul_mem (hbase a)
          (S.pow_mem
            (Algebra.subset_adjoin
              (Set.mem_insert_iff.mpr
                (Or.inr
                  (Set.mem_singleton
                    N13SpecialInfinityChart.vClass)))) n)
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13ReciprocalInfinityContraction.instFactPrimeOfNatNat_fLT
private theorem specialInfinity_quotient_coordinate_adjoin_eq_top
    (J : Ideal SpecialRing) :
    Algebra.adjoin k
        ({Ideal.Quotient.mk J N13SpecialInfinityChart.tClass,
          Ideal.Quotient.mk J N13SpecialInfinityChart.vClass} :
          Set (SpecialRing ⧸ J)) =
      ⊤ := by
  let π : SpecialRing →ₐ[k] SpecialRing ⧸ J :=
    Ideal.Quotient.mkₐ k J
  rw [show
      ({Ideal.Quotient.mk J N13SpecialInfinityChart.tClass,
        Ideal.Quotient.mk J N13SpecialInfinityChart.vClass} :
        Set (SpecialRing ⧸ J)) =
        π ''
          ({N13SpecialInfinityChart.tClass,
            N13SpecialInfinityChart.vClass} :
            Set SpecialRing) by
      exact (Set.image_pair π _ _).symm]
  rw [← AlgHom.map_adjoin,
    specialInfinity_coordinate_adjoin_eq_top,
    Algebra.map_top, AlgHom.range_eq_top]
  exact Ideal.Quotient.mk_surjective
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem reduceInfinityQuotient_surjective
    (I : Ideal InfinityRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map N13IntegralInfinityReduction.reduceCoordinate I =
        J) :
    Function.Surjective (reduceInfinityQuotient I J hmap) :=
  N13QuotientReduction.inducedQuotientMap_surjective
    N13IntegralInfinityReduction.reduceCoordinate
    N13IntegralInfinityReduction.reduceCoordinate_surjective
    I J hmap
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem ker_reduceInfinityQuotient_eq_span_two
    (I : Ideal InfinityRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map N13IntegralInfinityReduction.reduceCoordinate I =
        J) :
    RingHom.ker (reduceInfinityQuotient I J hmap) =
      Ideal.span
        ({algebraMap R₂ (InfinityRing ⧸ I) (2 : R₂)} :
          Set (InfinityRing ⧸ I)) := by
  simpa only [reduceInfinityQuotient,
    Ideal.Quotient.mk_algebraMap] using
    (N13QuotientReduction.ker_inducedQuotientMap_eq_span
      N13IntegralInfinityReduction.reduceCoordinate
      N13IntegralInfinityReduction.reduceCoordinate_surjective
      I J hmap
      (algebraMap R₂ InfinityRing (2 : R₂))
      N13IntegralInfinityReduction.ker_reduceCoordinate)
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13ReciprocalInfinityContraction.baseSpecialAlgebra MazurProof.N13ReciprocalInfinityContraction.instFactPrimeOfNatNat_fLT
theorem specialQuotientMap_comp_algebraMap
    (I : Ideal InfinityRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map N13IntegralInfinityReduction.reduceCoordinate I =
        J) :
    (reduceInfinityQuotient I J hmap).comp
        (algebraMap R₂ (InfinityRing ⧸ I)) =
      (algebraMap k (SpecialRing ⧸ J)).comp
        (algebraMap R₂ k) := by
  ext r
  change
    Ideal.Quotient.mk J
        (N13IntegralInfinityReduction.reduceCoordinate
          (algebraMap R₂ InfinityRing r)) =
      Ideal.Quotient.mk J
        (algebraMap k SpecialRing
          (N13IntegralInfinityReduction.reduceBase r))
  congr 1
  change
    N13IntegralInfinityReduction.reduceCoordinate
        (N13IntegralInfinityReduction.integralBaseClass (C r)) =
      N13IntegralInfinityReduction.specialBaseClass
        (C (N13IntegralInfinityReduction.reduceBase r))
  rw [N13IntegralInfinityReduction.reduce_integralBaseClass]
  simp [N13IntegralInfinityReduction.reducePoly]
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13ReciprocalInfinityContraction.baseSpecialAlgebra MazurProof.N13ReciprocalInfinityContraction.instFactPrimeOfNatNat_fLT
theorem exists_integralInfinity_basis_oneT_or_oneV
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (hfinite :
      Module.Finite R₂
        (InfinityRing ⧸ integralInfinityIdeal D hdeg h0)) :
    (∃ bT : Basis (Fin 2) R₂
        (InfinityRing ⧸ integralInfinityIdeal D hdeg h0),
      (bT : Fin 2 →
        InfinityRing ⧸ integralInfinityIdeal D hdeg h0) =
        N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk
            (integralInfinityIdeal D hdeg h0)
            N13IntegralInfinityChart.tClass)) ∨
      (∃ bV : Basis (Fin 2) R₂
        (InfinityRing ⧸ integralInfinityIdeal D hdeg h0),
      (bV : Fin 2 →
        InfinityRing ⧸ integralInfinityIdeal D hdeg h0) =
        N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk
            (integralInfinityIdeal D hdeg h0)
            N13IntegralInfinityChart.vClass)) := by
  let I := integralInfinityIdeal D hdeg h0
  let J : Ideal SpecialRing :=
    Ideal.map N13IntegralInfinityReduction.reduceCoordinate I
  let B := InfinityRing ⧸ I
  let C := SpecialRing ⧸ J
  let g : B →+* C :=
    reduceInfinityQuotient I J rfl
  letI : Module.Finite R₂ B := hfinite
  letI : Module.Flat R₂ B :=
    integralInfinityQuotient_flat D hdeg h0
  letI : Module.Free R₂ B :=
    Module.free_of_flat_of_isLocalRing
  letI : IsScalarTower R₂ k C :=
    IsScalarTower.of_algebraMap_eq
      (R := R₂) (S := k) (A := C) fun _ => rfl
  have hfactor :
      g.comp (algebraMap R₂ B) =
        (algebraMap k C).comp (algebraMap R₂ k) := by
    exact specialQuotientMap_comp_algebraMap I J rfl
  have hg : Function.Surjective g :=
    reduceInfinityQuotient_surjective I J rfl
  have hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R₂ B (2 : R₂)} : Set B) :=
    ker_reduceInfinityQuotient_eq_span_two I J rfl
  let eK : k ⊗[R₂] B ≃ₗ[k] C :=
    N13TensorSpecialFiber.tensorLinearEquiv
      (g := g)
      (hfactor := hfactor)
      (hq := ZMod.ringHom_surjective PadicInt.toZMod)
      (π := (2 : R₂))
      (hπ := N13IntegralInfinityReduction.reduceBase_two)
      (hg := hg)
      (hker := hker)
  have hfinB : Module.finrank R₂ B = 2 :=
    integralInfinityQuotient_finrank_eq_two
      D hdeg h0 hfinite
  have hfinC : Module.finrank k C = 2 := by
    rw [← eK.finrank_eq, Module.finrank_baseChange, hfinB]
  letI : Nontrivial C :=
    Module.nontrivial_of_finrank_pos
      (R := k) (M := C) (by rw [hfinC]; decide)
  let tB : B :=
    Ideal.Quotient.mk I N13IntegralInfinityChart.tClass
  let vB : B :=
    Ideal.Quotient.mk I N13IntegralInfinityChart.vClass
  let tC : C :=
    Ideal.Quotient.mk J N13SpecialInfinityChart.tClass
  let vC : C :=
    Ideal.Quotient.mk J N13SpecialInfinityChart.vClass
  have hgen :
      Algebra.adjoin k ({tC, vC} : Set C) = ⊤ :=
    specialInfinity_quotient_coordinate_adjoin_eq_top J
  have hexC :=
    N13TwoGeneratorFiberBasis.exists_basis_oneX_or_oneY
      tC vC hfinC hgen
  have hfactorκ :
      g.comp (algebraMap R₂ B) =
        (algebraMap κ C).comp (IsLocalRing.residue R₂) := by
    ext r
    calc
      g (algebraMap R₂ B r) =
          algebraMap k C (algebraMap R₂ k r) := by
        simpa only [RingHom.comp_apply] using
          DFunLike.congr_fun hfactor r
      _ = algebraMap R₂ C r :=
        (IsScalarTower.algebraMap_apply R₂ k C r).symm
      _ = algebraMap κ C (algebraMap R₂ κ r) :=
        IsScalarTower.algebraMap_apply R₂ κ C r
      _ = algebraMap κ C
          (IsLocalRing.residue R₂ r) := by
        rfl
  have htwo :
      (2 : R₂) ∈ IsLocalRing.maximalIdeal R₂ := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span (Set.mem_singleton (2 : R₂))
  let eκ : κ ⊗[R₂] B ≃ₗ[κ] C :=
    N13TensorSpecialFiber.residueLinearEquiv
      g hfactorκ (2 : R₂) htwo hg hker
  have eκ_tmul_one (z : B) :
      eκ (TensorProduct.mk R₂ κ B 1 z) = g z := by
    change
      (N13TensorSpecialFiber.residueLinearEquiv
        g hfactorκ (2 : R₂) htwo hg hker)
          ((1 : κ) ⊗ₜ[R₂] z) = g z
    simpa only [one_smul] using
      (N13TensorSpecialFiber.residueLinearEquiv_tmul
        (g := g) (hfactor := hfactorκ)
        (π := (2 : R₂))
        (hπ := htwo)
        (hg := hg) (hker := hker)
        (1 : κ) z)
  have hκk :
      Function.Surjective (algebraMap κ k) := by
    intro a
    obtain ⟨r, hr⟩ :=
      ZMod.ringHom_surjective PadicInt.toZMod a
    refine ⟨IsLocalRing.residue R₂ r, ?_⟩
    calc
      algebraMap κ k (IsLocalRing.residue R₂ r) =
          algebraMap R₂ k r := by
        exact
          (IsScalarTower.algebraMap_apply R₂ κ k r).symm
      _ = a := hr
  have ht_map : g tB = tC := by
    change
      reduceInfinityQuotient I J rfl
          (Ideal.Quotient.mk I
            N13IntegralInfinityChart.tClass) =
        tC
    rw [reduceInfinityQuotient_mk,
      N13IntegralInfinityReduction.reduce_tClass]
  have hv_map : g vB = vC := by
    change
      reduceInfinityQuotient I J rfl
          (Ideal.Quotient.mk I
            N13IntegralInfinityChart.vClass) =
        vC
    rw [reduceInfinityQuotient_mk,
      N13IntegralInfinityReduction.reduce_vClass]
  rcases hexC with ⟨bC, hbC⟩ | ⟨bC, hbC⟩
  · left
    obtain ⟨bCκ, hbCκ⟩ :=
      N13ContractQuotientXYBasis.exists_basis_restrictScalars_of_surjective
        hκk bC
    let b₀ : Basis (Fin 2) κ (κ ⊗[R₂] B) :=
      N13TensorSpecialFiber.pullbackBasis eκ bCκ
    have heval (i : Fin 2) :
        eκ (TensorProduct.mk R₂ κ B 1
          (N13FiniteFlatBasisLift.oneX tB i)) =
          bCκ i := by
      rw [eκ_tmul_one]
      fin_cases i
      · simpa [N13FiniteFlatBasisLift.oneX] using
          (congrFun hbC (0 : Fin 2)).symm.trans
            (congrFun hbCκ (0 : Fin 2)).symm
      · simpa [N13FiniteFlatBasisLift.oneX, ht_map] using
          (congrFun hbC (1 : Fin 2)).symm.trans
            (congrFun hbCκ (1 : Fin 2)).symm
    have hb₀ (i : Fin 2) :
        TensorProduct.mk R₂ κ B 1
            (N13FiniteFlatBasisLift.oneX tB i) =
          b₀ i :=
      N13TensorSpecialFiber.mk_eq_pullbackBasis
        eκ (N13FiniteFlatBasisLift.oneX tB) bCκ heval i
    simpa [I, B, tB] using
      N13FiniteFlatBasisLift.exists_basis_oneX
        (R := R₂) (B := B) tB b₀ hb₀
  · right
    obtain ⟨bCκ, hbCκ⟩ :=
      N13ContractQuotientXYBasis.exists_basis_restrictScalars_of_surjective
        hκk bC
    let b₀ : Basis (Fin 2) κ (κ ⊗[R₂] B) :=
      N13TensorSpecialFiber.pullbackBasis eκ bCκ
    have heval (i : Fin 2) :
        eκ (TensorProduct.mk R₂ κ B 1
          (N13FiniteFlatBasisLift.oneX vB i)) =
          bCκ i := by
      rw [eκ_tmul_one]
      fin_cases i
      · simpa [N13FiniteFlatBasisLift.oneX] using
          (congrFun hbC (0 : Fin 2)).symm.trans
            (congrFun hbCκ (0 : Fin 2)).symm
      · simpa [N13FiniteFlatBasisLift.oneX, hv_map] using
          (congrFun hbC (1 : Fin 2)).symm.trans
            (congrFun hbCκ (1 : Fin 2)).symm
    have hb₀ (i : Fin 2) :
        TensorProduct.mk R₂ κ B 1
            (N13FiniteFlatBasisLift.oneX vB i) =
          b₀ i :=
      N13TensorSpecialFiber.mk_eq_pullbackBasis
        eκ (N13FiniteFlatBasisLift.oneX vB) bCκ heval i
    simpa [I, B, vB] using
      N13FiniteFlatBasisLift.exists_basis_oneX
        (R := R₂) (B := B) vB b₀ hb₀
end
end MazurProof.N13ReciprocalInfinityContraction
end
end


set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem solution
    (D : MazurProof.SexticMumford.Mumford MazurProof.N13ReciprocalInfinityContraction.Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (hfinite :
      Module.Finite MazurProof.N13ReciprocalInfinityContraction.R₂
        (MazurProof.N13ReciprocalInfinityContraction.InfinityRing ⧸ MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal D hdeg h0)) :
    (∃ bT : Basis (Fin 2) MazurProof.N13ReciprocalInfinityContraction.R₂
        (MazurProof.N13ReciprocalInfinityContraction.InfinityRing ⧸ MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal D hdeg h0),
      (bT : Fin 2 →
        MazurProof.N13ReciprocalInfinityContraction.InfinityRing ⧸ MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal D hdeg h0) =
        MazurProof.N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk
            (MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal D hdeg h0)
            MazurProof.N13IntegralInfinityChart.tClass)) ∨
      (∃ bV : Basis (Fin 2) MazurProof.N13ReciprocalInfinityContraction.R₂
        (MazurProof.N13ReciprocalInfinityContraction.InfinityRing ⧸ MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal D hdeg h0),
      (bV : Fin 2 →
        MazurProof.N13ReciprocalInfinityContraction.InfinityRing ⧸ MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal D hdeg h0) =
        MazurProof.N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk
            (MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal D hdeg h0)
            MazurProof.N13IntegralInfinityChart.vClass)) := by
  exact MazurProof.N13ReciprocalInfinityContraction.exists_integralInfinity_basis_oneT_or_oneV D hdeg h0 hfinite
