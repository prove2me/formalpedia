-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_isLocalBridge1_padicAlgCl
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/37872e5d-791b-57d1-b4eb-ff82ccf23040

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_LocalBridge
import Theorems.Thm_groupCohomology_exists_isLocalBridge1
import Theorems.Thm_groupCohomology_isLocalBridge1_apply_eq_zero_iff
import Theorems.Thm_groupCohomology_isLocalBridge1_mem_continuousH1_and_exists_eq
import Theorems.Thm_Rep_nonempty_res_free_iso_free
import Theorems.Thm_NumberField_PlaceDecomp_exists_extension_fixed_of_injective_padicAlgCl
import Theorems.Thm_NumberField_PlaceDecomp_exists_unit_map_eq_of_forall_apply_eq_padicAlgCl
import Theorems.Thm_NumberField_PlaceDecomp_exists_fixed_d01_eq_of_isLevelConstant1_padicAlgCl
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_exists_isLocalBridge1_padicAlgCl
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

namespace ReduceA5

section generic

attribute [local instance 10] AddCommGroup.toIntModule

def linOfAdd {V W : Type} [AddCommGroup V] [AddCommGroup W] {_ : Module ℤ V} {_ : Module ℤ W} (ψ : V →+ W) : V →ₗ[ℤ] W where
  toFun := ψ
  map_add' := ψ.map_add
  map_smul' c x := map_intCast_smul ψ ℤ ℤ c x

theorem finite_of_iso_free {D : Type} [Group D] {β : Type} {P : Rep ℤ D} [Module.Finite ℤ P]
    (e : P ≅ Rep.free ℤ D β) : Finite β := by
  haveI : Module.Finite ℤ (Rep.free ℤ D β) := Module.Finite.equiv (Representation.equivOfIso e).toLinearEquiv
  have b := Finsupp.basis (R := ℤ) (ι := β)
    (fun _ => ((Finsupp.basisSingleOne : Module.Basis D ℤ (D →₀ ℤ)).map (MonoidAlgebra.coeffLinearEquiv ℤ).symm))
  haveI := Module.Finite.finite_basis b
  exact Finite.of_injective (fun x : β => (⟨x, 1⟩ : Σ _ : β, D)) (fun _ _ h => congrArg Sigma.fst h)

section ihomTransport

variable {D H : Type} [Group D] [Group H] (π : H →* D) {P P' : Rep ℤ D} (e : P ≅ P') (A : Rep ℤ H)

noncomputable def preHom : ((ihom (Rep.res π P')).obj A) →+ ((ihom (Rep.res π P)).obj A) where
  toFun χ := (show P'.V →ₗ[ℤ] A.V from χ) ∘ₗ e.hom.hom.toLinearMap
  map_zero' := LinearMap.zero_comp _
  map_add' _ _ := LinearMap.add_comp _ _ _

noncomputable def preInv : ((ihom (Rep.res π P)).obj A) →+ ((ihom (Rep.res π P')).obj A) where
  toFun χ := (show P.V →ₗ[ℤ] A.V from χ) ∘ₗ e.inv.hom.toLinearMap
  map_zero' := LinearMap.zero_comp _
  map_add' _ _ := LinearMap.add_comp _ _ _

theorem preHom_apply (χ : (ihom (Rep.res π P')).obj A) (x : P) :
    LinearMap.toAddMonoidHom (preHom π e A χ) x = LinearMap.toAddMonoidHom χ (e.hom.hom x) := rfl

theorem preInv_apply (χ : (ihom (Rep.res π P)).obj A) (x : P') :
    LinearMap.toAddMonoidHom (preInv π e A χ) x = LinearMap.toAddMonoidHom χ (e.inv.hom x) := rfl

theorem preHom_preInv (χ : (ihom (Rep.res π P)).obj A) : preHom π e A (preInv π e A χ) = χ :=
  LinearMap.ext fun x => congrArg (show P.V →ₗ[ℤ] A.V from χ) (Rep.inv_hom_apply _ _ e x)

theorem preHom_ρ (h : H) (χ : (ihom (Rep.res π P')).obj A) :
    preHom π e A (((ihom (Rep.res π P')).obj A).ρ h χ) = ((ihom (Rep.res π P)).obj A).ρ h (preHom π e A χ) := by
  apply LinearMap.ext
  intro x
  change A.ρ h ((show P'.V →ₗ[ℤ] A.V from χ) (P'.ρ (π h⁻¹) (e.hom.hom x))) =
    A.ρ h ((show P'.V →ₗ[ℤ] A.V from χ) (e.hom.hom (P.ρ (π h⁻¹) x)))
  exact congrArg (fun y => A.ρ h ((show P'.V →ₗ[ℤ] A.V from χ) y)) (Rep.hom_comm_apply e.hom (π h⁻¹) x).symm

theorem preInv_ρ (h : H) (χ : (ihom (Rep.res π P)).obj A) :
    preInv π e A (((ihom (Rep.res π P)).obj A).ρ h χ) = ((ihom (Rep.res π P')).obj A).ρ h (preInv π e A χ) := by
  apply LinearMap.ext
  intro x
  change A.ρ h ((show P.V →ₗ[ℤ] A.V from χ) (P.ρ (π h⁻¹) (e.inv.hom x))) =
    A.ρ h ((show P.V →ₗ[ℤ] A.V from χ) (e.inv.hom (P'.ρ (π h⁻¹) x)))
  exact congrArg (fun y => A.ρ h ((show P.V →ₗ[ℤ] A.V from χ) y)) (Rep.hom_comm_apply e.inv (π h⁻¹) x).symm

noncomputable def preInvCocycle (u : cocycles₁ ((ihom (Rep.res π P)).obj A)) : cocycles₁ ((ihom (Rep.res π P')).obj A) :=
  ⟨fun h => preInv π e A (u h), (mem_cocycles₁_iff _).2 fun g h => by
    have hu := (mem_cocycles₁_iff (u : H → (ihom (Rep.res π P)).obj A)).1 u.2 g h
    change preInv π e A (u (g * h)) = _
    rw [hu, map_add, preInv_ρ]⟩

theorem preInvCocycle_apply (u : cocycles₁ ((ihom (Rep.res π P)).obj A)) (h : H) :
    (preInvCocycle π e A u : H → _) h = preInv π e A (u h) := rfl

end ihomTransport

theorem free_and_finite_int {G : Type} [Group G] [Finite G] {α : Type} [Finite α] {P : Rep ℤ G} (eP : P ≅ Rep.free ℤ G α) :
    @Module.Free ℤ P _ _ (AddCommGroup.toIntModule _) ∧ @Module.Finite ℤ P _ _ (AddCommGroup.toIntModule _) ∧
      @Module.Finite ℤ P _ _ P.hV2 := by
  haveI h1 : Module.Finite ℤ P := Module.Finite.equiv (Representation.equivOfIso eP).toLinearEquiv.symm
  haveI h2 : Module.Free ℤ P := Module.Free.of_equiv (Representation.equivOfIso eP).toLinearEquiv.symm
  refine ⟨?_, ?_, h1⟩
  · convert h2; exact Subsingleton.elim _ _
  · convert h1; exact Subsingleton.elim _ _

end generic

section main
attribute [local instance 10] AddCommGroup.toIntModule

set_option maxHeartbeats 16000000 in
theorem main
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact ((q : ℕ)).Prime]
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hΦF : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (hcont : Continuous Φ)
    (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (hπsurj : Function.Surjective π)
    (heqv : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))
    {R P B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)} (f : R ⟶ P) (g : P ⟶ B)
    (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    (α : Type) [Finite α] (eP : P ≅ Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) α) (hB : ∀ b : B, p • b = 0)
    (κ : B →+ M →+ Additive (PadicAlgCl q)ˣ)
    (hκeq : ∀ (τ : primeLocalGaloisGroup q) (b : B) (m : M),
      κ (B.ρ ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) b) (M.ρ (primeLocalToGlobal q τ) m) =
        (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (κ b m))
    (hκ : ∀ c : B →+ Additive (PadicAlgCl q)ˣ, ∃! m : M, ∀ b, κ b m = c b) :
    ∃ Λ : (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R ⟶
          Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) →+
        H1 (Rep.res (primeLocalToGlobal q) M),
      IsLocalBridge₁ π ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f)
        ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map g)
        (X := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
        (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
        (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive (M := Rep.res (primeLocalToGlobal q) M) κ Λ ∧
      (∀ φ, Λ φ = 0 ↔ ∃ χ : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype P ⟶
          Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ,
        (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f ≫ χ = φ) ∧
      (∀ φ, Λ φ ∈ continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)) ∧
      (∀ y ∈ continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M), ∃ φ, Λ φ = y) := by
  classical

  have hmem : ∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) ∈ NumberField.PlaceDecomp.decomp ℚ ↥F w := fun τ => by
    have h := (π τ).2; rw [hπ τ] at h; exact h
  have hsurj' : ∀ d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w), ∃ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) := fun d => by
    obtain ⟨τ, rfl⟩ := hπsurj d; exact ⟨τ, hπ τ⟩
  have heqv' : ∀ (d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q),
      (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) →
      ∀ x : w.adicCompletion ↥F, Φ (d • x) = τ (Φ x) := fun d τ hd x => by
    have : d = π τ := Subtype.ext (hd.trans (hπ τ).symm)
    subst this; exact heqv τ x
  have hKR := NumberField.PlaceDecomp.exists_extension_fixed_of_injective_padicAlgCl (q : ℕ) F w σ Φ hΦF hmem hsurj' heqv' hcont
  have hFIX := NumberField.PlaceDecomp.exists_unit_map_eq_of_forall_apply_eq_padicAlgCl (q : ℕ) F w σ Φ hΦF hmem hsurj' heqv' hcont
  have hH90 := NumberField.PlaceDecomp.exists_fixed_d01_eq_of_isLevelConstant1_padicAlgCl (q : ℕ) F w σ Φ hΦF hmem hsurj' heqv' hcont

  have hπlev : ∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F' ∧
      ∀ s : primeLocalGaloisGroup q, primeLocalToGlobal q s ∈ F'.fixingSubgroup → π s = 1 := by
    have hrNH : ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, g ∈ F.fixingSubgroup → AlgEquiv.restrictNormalHom ↥F g = 1 := by
      intro g hg
      ext x
      change algebraMap ↥F (AlgebraicClosure ℚ) (AlgEquiv.restrictNormalHom ↥F g x) = ((1 : ↥F ≃ₐ[ℚ] ↥F) x : AlgebraicClosure ℚ)
      rw [AlgEquiv.one_apply]
      exact (AlgEquiv.restrictNormal_commutes g ↥F x).trans ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x.1 x.2)
    refine ⟨F, inferInstance, fun s hs => Subtype.ext ?_⟩
    rw [hπ s]
    change AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q s * σ) = 1
    rw [map_mul, map_mul, hrNH _ hs, mul_one, ← map_mul, inv_mul_cancel, map_one]

  have hι : Function.Injective ((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive) := by
    intro a b h
    have h' : Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) (Additive.toMul a) =
        Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) (Additive.toMul b) := congrArg Additive.toMul h
    have h'' : Φ ((Additive.toMul a : (w.adicCompletion ↥F)ˣ) : w.adicCompletion ↥F) =
        Φ ((Additive.toMul b : (w.adicCompletion ↥F)ˣ) : w.adicCompletion ↥F) := congrArg Units.val h'
    exact congrArg Additive.ofMul (Units.ext (Φ.injective h''))
  have hιeq : ∀ (h : primeLocalGaloisGroup q) (x : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ),
      (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive
          ((Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ).ρ (π h) x) =
        (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ h
          ((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive x) := by
    intro τ x
    obtain ⟨u, rfl⟩ : ∃ v : (w.adicCompletion ↥F)ˣ, Additive.ofMul v = x := ⟨Additive.toMul x, rfl⟩
    change (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive
        ((Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ).ρ (π τ) (Additive.ofMul u)) =
      (Rep.ofMulDistribMulAction (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) (PadicAlgCl q)ˣ).ρ
        (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ)
        (Additive.ofMul (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) u))
    rw [Rep.ofMulDistribMulAction_ρ_apply_apply, Rep.ofMulDistribMulAction_ρ_apply_apply]
    apply congrArg Additive.ofMul
    apply Units.ext
    change Φ (((π τ • u : (w.adicCompletion ↥F)ˣ)) : w.adicCompletion ↥F) =
      (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ (u : w.adicCompletion ↥F))
    rw [NumberField.PlaceDecomp.coe_smul_units]
    exact heqv τ u
  have hιfix : ∀ a : (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)),
      (∀ s : primeLocalGaloisGroup q, π s = 1 →
        (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ s a = a) →
      ∃ x : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ,
        (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive x = a := by
    intro a ha
    obtain ⟨x, hx⟩ := hFIX (Additive.toMul a) (fun τ hτ => by
      have h1 : π τ = 1 := Subtype.ext ((hπ τ).trans hτ)
      have h2 := ha τ h1
      change (Rep.ofMulDistribMulAction (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) (PadicAlgCl q)ˣ).ρ
          (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Additive.ofMul (Additive.toMul a)) = Additive.ofMul (Additive.toMul a) at h2
      rw [Rep.ofMulDistribMulAction_ρ_apply_apply] at h2
      exact congrArg Units.val (Additive.ofMul.injective h2))
    refine ⟨Additive.ofMul x, ?_⟩
    change Additive.ofMul (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) x) = a
    rw [show Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) x = Additive.toMul a from Units.ext hx]
    rfl

  haveI : Finite (↥F ≃ₐ[ℚ] ↥F) := inferInstance
  obtain ⟨hfreeW, hfinW, hfinP⟩ := free_and_finite_int eP

  have hdiv : ∀ φ : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R ⟶
        Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ,
      ∃ ψ : (ihom (Rep.res π (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype P))).obj
          (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)),
        (∀ x : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R,
          LinearMap.toAddMonoidHom ψ (((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f).hom x) =
            (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive (φ.hom x)) ∧
        ∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F' ∧
          ∀ s : primeLocalGaloisGroup q, primeLocalToGlobal q s ∈ F'.fixingSubgroup →
            ∀ x : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype P,
              (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ s (LinearMap.toAddMonoidHom ψ x) =
                LinearMap.toAddMonoidHom ψ x := by
    intro φ
    obtain ⟨ψ, hψ1, F₂, hF₂, hψ2⟩ := @hKR R P _ _ hfreeW hfinW f.hom.toLinearMap.toAddMonoidHom.toIntLinearMap
      (fun a b h => hf h) φ.hom.toLinearMap.toAddMonoidHom.toIntLinearMap
    exact ⟨linOfAdd ψ.toAddMonoidHom, fun x => hψ1 x, F₂, hF₂, fun s hs x => hψ2 s hs x⟩
  have hdiv₀ : ∀ φ : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R ⟶
        Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ,
      ∃ ψ : (ihom (Rep.res π (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype P))).obj
          (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)),
        ∀ x : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R,
          LinearMap.toAddMonoidHom ψ (((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f).hom x) =
            (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive (φ.hom x) := fun φ => by
    obtain ⟨ψ, h1, -⟩ := hdiv φ; exact ⟨ψ, h1⟩

  have h90 : ∀ u : cocycles₁ ((ihom (Rep.res π (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype P))).obj
          (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))),
      IsLevelConstant₁ (primeLocalToGlobal q) (u : primeLocalGaloisGroup q → _) →
      ∃ χ : (ihom (Rep.res π (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype P))).obj
          (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)),
        (∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F' ∧
          ∀ s : primeLocalGaloisGroup q, primeLocalToGlobal q s ∈ F'.fixingSubgroup →
            ∀ x : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype P,
              (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ s (LinearMap.toAddMonoidHom χ x) =
                LinearMap.toAddMonoidHom χ x) ∧
        (d₀₁ _).hom χ = (u : primeLocalGaloisGroup q → _) := by
    intro u hu
    obtain ⟨βT, ⟨e₀⟩⟩ := Rep.nonempty_res_free_iso_free (k := ℤ) (NumberField.PlaceDecomp.decomp ℚ ↥F w) α
    let e : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype P ≅ Rep.free ℤ ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) βT :=
      (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).mapIso eP ≪≫ e₀
    haveI : Finite βT := @finite_of_iso_free _ _ βT (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype P) hfinP e
    let A' : Rep ℤ (primeLocalGaloisGroup q) := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))
    let u' := preInvCocycle π e A' u
    have hu' : IsLevelConstant₁ (primeLocalToGlobal q) (u' : primeLocalGaloisGroup q → _) := by
      obtain ⟨F₁, hF₁, h⟩ := hu
      exact ⟨F₁, hF₁, fun g s hs => by
        change preInv π e A' (u (g * s)) = preInv π e A' (u g)
        rw [h g s hs]⟩
    obtain ⟨χ', ⟨F₂, hF₂, hfix⟩, hd⟩ := hH90 βT π hπ u' hu'
    refine ⟨preHom π e A' χ', ⟨F₂, hF₂, fun s hs x => hfix s hs (e.hom.hom x)⟩, ?_⟩
    funext h
    have hdh := congrFun hd h
    rw [d₀₁_hom_apply] at hdh ⊢
    change _ = preInv π e A' (u h) at hdh
    calc _ = preHom π e A' (((ihom (Rep.res π (Rep.free ℤ ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) βT))).obj A').ρ h χ') -
          preHom π e A' χ' :=
          congrArg (fun t => t - preHom π e A' χ') (preHom_ρ π e A' h χ').symm
      _ = preHom π e A' (preInv π e A' (u h)) := by
          rw [← map_sub]; exact congrArg (preHom π e A') hdh
      _ = u h := preHom_preInv π e A' (u h)

  obtain ⟨Λ, hΛ⟩ := groupCohomology.exists_isLocalBridge1 π
    ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f)
    ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map g) hfg hg
    (X := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
    (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
    ((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive) hι hιeq
    (M := Rep.res (primeLocalToGlobal q) M) κ hκeq hκ hdiv₀
  refine ⟨Λ, hΛ, fun φ => ?_, ?_⟩
  · exact groupCohomology.isLocalBridge1_apply_eq_zero_iff π hπsurj
      ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f)
      ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map g) hfg hg
      (X := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
      (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
      ((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive) hι hιeq hιfix
      (M := Rep.res (primeLocalToGlobal q) M) κ hκeq hκ hdiv₀ hΛ φ
  · exact groupCohomology.isLocalBridge1_mem_continuousH1_and_exists_eq (primeLocalToGlobal q) π hπsurj hπlev
      ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f)
      ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map g) hfg hg
      (X := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
      (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
      ((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive) hι hιeq hιfix
      (M := Rep.res (primeLocalToGlobal q) M) κ hκeq hκ hdiv h90 hΛ

end main

end ReduceA5

theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact ((q : ℕ)).Prime]
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hΦF : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (hcont : Continuous Φ)
    (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (hπsurj : Function.Surjective π)
    (heqv : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))
    {R P B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)} (f : R ⟶ P) (g : P ⟶ B)
    (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    (α : Type) [Finite α] (eP : P ≅ Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) α) (hB : ∀ b : B, p • b = 0)
    (κ : B →+ M →+ Additive (PadicAlgCl q)ˣ)
    (hκeq : ∀ (τ : primeLocalGaloisGroup q) (b : B) (m : M),
      κ (B.ρ ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) b) (M.ρ (primeLocalToGlobal q τ) m) =
        (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (κ b m))
    (hκ : ∀ c : B →+ Additive (PadicAlgCl q)ˣ, ∃! m : M, ∀ b, κ b m = c b) :
    ∃ Λ : (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R ⟶
          Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) →+
        H1 (Rep.res (primeLocalToGlobal q) M),
      IsLocalBridge₁ π ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f)
        ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map g)
        (X := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
        (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
        (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive (M := Rep.res (primeLocalToGlobal q) M) κ Λ ∧
      (∀ φ, Λ φ = 0 ↔ ∃ χ : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype P ⟶
          Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ,
        (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f ≫ χ = φ) ∧
      (∀ φ, Λ φ ∈ continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)) ∧
      (∀ y ∈ continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M), ∃ φ, Λ φ = y) :=
  ReduceA5.main q M F w σ Φ hΦF hcont π hπ hπsurj heqv f g hf hfg hg α eP hB κ hκeq hκ

end S_NumberField_PlaceDecomp_exists_isLocalBridge1_padicAlgCl
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_isLocalBridge1_padicAlgCl (solution)
