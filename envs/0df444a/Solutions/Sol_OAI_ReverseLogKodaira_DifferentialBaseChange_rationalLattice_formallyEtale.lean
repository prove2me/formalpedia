-- Prove2me | solution 1 for OAI.ReverseLogKodaira.DifferentialBaseChange.rationalLattice_formallyEtale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:10:05.540704+00:00
-- url     : https://prove2.me/submissions/64ec345e-bfa7-45e1-9a90-700a2995754e

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/LatticeBaseChange.lean:L213-L232
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.DifferentialBaseChange.rationalLattice_formallyEtale. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_FiberCharts
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LatticeBaseChange

-- ---- from OAI.AlgebraicGeometry.LogKodaira.LatticeBaseChange ----
-- Backport the two-case eliminator from Mathlib/LinearAlgebra/TensorProduct/Defs.lean
-- at d13f23b723b8a846827a245b89c10fc7d3f11612, using the 4.33.1 eliminator.
section Lean433TensorProductCompatibility
open scoped TensorProduct
variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
namespace TensorProduct
@[elab_as_elim, induction_eliminator]
protected theorem inductionOn {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (tmul : ∀ x y, motive (x ⊗ₜ[R] y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z
    (by simpa only [TensorProduct.zero_tmul] using tmul (0 : M) (0 : N)) tmul add
end TensorProduct
end Lean433TensorProductCompatibility

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.DifferentialBaseChange
section Span
variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
  [IsScalarTower A B N]

lemma exterior_span_of_span (f : M →ₗ[A] N)
    (hf : Submodule.span B (Set.range f) = ⊤) (n : ℕ) :
    Submodule.span B (Set.range (exteriorScalarMap A B M N f n)) = ⊤ := by
  apply top_unique
  rw [← exteriorPower.ιMulti_span_of_span B n N hf, Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  have hv' : ∀ i, ∃ u, f u = v i := fun i => hv ⟨i, rfl⟩
  choose u hu using hv'
  apply Submodule.subset_span
  refine ⟨exteriorPower.ιMulti A n u, ?_⟩
  simp only [exteriorScalarMap, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  change exteriorPower.ιMulti B n (f ∘ u) = exteriorPower.ιMulti B n v
  exact congrArg (exteriorPower.ιMulti B n) (funext hu)

lemma tensor_span_of_span (f : M →ₗ[A] N)
    (hf : Submodule.span B (Set.range f) = ⊤) (m : ℕ) :
    Submodule.span B (Set.range (tensorScalarMap A B M N f m)) = ⊤ := by
  have ht : Submodule.span B (Set.range fun a : Fin m → M =>
      PiTensorProduct.tprod B fun j => f (a j)) = ⊤ :=
    PiTensorProduct.submodule_span_eq_top (R := B) (M := fun _ : Fin m => N)
      (γ := fun _ => M) (g := fun {i} a => f a) (fun _ => hf)
  apply top_unique
  rw [← ht, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  apply Submodule.subset_span
  refine ⟨PiTensorProduct.tprod A v, ?_⟩
  simp only [tensorScalarMap, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply]
  rfl

end Span

 

theorem formallyEtale_pluricanonical_span
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallyEtale A B] (n m : ℕ) :
    Submodule.span B ((LinearMap.range (pluricanonicalMap R R A B n m)) :
      Set (Pluricanonical R B n m)) = ⊤ := by
  have h : Submodule.span B (Set.range (KaehlerDifferential.map R R A B)) = ⊤ := by
    have he : (KaehlerDifferential.map R R A B).liftBaseChange B =
        (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).toLinearMap := by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul t x =>
        simp only [LinearMap.liftBaseChange_tmul, LinearEquiv.coe_toLinearMap,
          KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
          KaehlerDifferential.mapBaseChange_tmul]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [← LinearMap.coe_range, ← LinearMap.range_liftBaseChange, he,
      LinearMap.range_eq_top]
    exact (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).surjective
  exact tensor_span_of_span _ (exterior_span_of_span _ h n) m

end ReverseLogKodaira.DifferentialBaseChange

namespace ReverseLogKodaira.DifferentialBaseChange

 

section LatticeProofs
variable (R A K : Type*) [CommRing R] [CommRing A] [CommRing K]
  [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K]

lemma span_wedges (n : ℕ) :
    Submodule.span A (Set.range fun a : Fin n → A =>
      exteriorPower.ιMulti A n fun i => KaehlerDifferential.D R A (a i)) = ⊤ := by
  have h := exteriorPower.ιMulti_span_of_span A n (KaehlerDifferential R A)
    (KaehlerDifferential.span_range_derivation R A)
  convert h using 2
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨fun i => KaehlerDifferential.D R A (a i), by
      rintro _ ⟨i, rfl⟩; exact ⟨a i, rfl⟩, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    have hv' : ∀ i, ∃ a, KaehlerDifferential.D R A a = v i :=
      fun i => hv ⟨i, rfl⟩
    choose a ha using hv'
    exact ⟨a, congrArg (exteriorPower.ιMulti A n) (funext ha)⟩

lemma pluri_symbol (n m : ℕ) (a : Fin m → Fin n → A) :
    pluricanonicalMap R R A K n m (PiTensorProduct.tprod A fun j =>
      exteriorPower.ιMulti A n fun i => KaehlerDifferential.D R A (a j i)) =
    PiTensorProduct.tprod K fun j => exteriorPower.ιMulti K n fun i =>
      KaehlerDifferential.D R K (algebraMap A K (a j i)) := by
  simp only [pluricanonicalMap, tensorScalarMap, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.coe_restrictScalars,
    exteriorDifferentialMap, exteriorScalarMap,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.compLinearMap_apply,
    KaehlerDifferential.map_D]
  rfl

lemma range_pluricanonicalMap (n m : ℕ) :
    LinearMap.range (pluricanonicalMap R R A K n m) = rationalLattice R A K n m := by
  have ht : Submodule.span A (Set.range fun a : Fin m → Fin n → A =>
      PiTensorProduct.tprod A fun j => exteriorPower.ιMulti A n fun i =>
        KaehlerDifferential.D R A (a j i)) = ⊤ :=
    PiTensorProduct.submodule_span_eq_top (R := A)
      (M := fun _ : Fin m => Canonical R A n) (γ := fun _ => Fin n → A)
      (g := fun {i} a => exteriorPower.ιMulti A n fun j => KaehlerDifferential.D R A (a j))
      (fun _ => span_wedges R A n)
  rw [LinearMap.range_eq_map, ← ht, Submodule.map_span]
  unfold rationalLattice
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (pluri_symbol R A K n m a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, pluri_symbol R A K n m a⟩

end LatticeProofs

lemma differential_map_fiber_tower
    (A B B' S C : Type*) [CommRing A] [CommRing B] [CommRing B']
    [CommRing S] [CommRing C]
    [Algebra A B] [Algebra A B'] [Algebra B B'] [IsScalarTower A B B']
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra B' C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A B' C] [IsScalarTower B B' C]
    [IsScalarTower A S C] (x : KaehlerDifferential A B) :
    KaehlerDifferential.map A S B' C (KaehlerDifferential.map A A B B' x) =
      KaehlerDifferential.map A S B C x := by
  have h : ((KaehlerDifferential.map A S B' C).restrictScalars B).comp
      (KaehlerDifferential.map A A B B') = KaehlerDifferential.map A S B C := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation A B)
    rintro _ ⟨b, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      KaehlerDifferential.map_D]
    rw [IsScalarTower.algebraMap_apply B B' C]
  exact LinearMap.congr_fun h x

lemma exterior_map_fiber_tower
    (A B B' S C : Type*) [CommRing A] [CommRing B] [CommRing B']
    [CommRing S] [CommRing C]
    [Algebra A B] [Algebra A B'] [Algebra B B'] [IsScalarTower A B B']
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra B' C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A B' C] [IsScalarTower B B' C]
    [IsScalarTower A S C] (r : ℕ) :
    ((exteriorDifferentialMap A S B' C r).restrictScalars B).comp
      (exteriorDifferentialMap A A B B' r) = exteriorDifferentialMap A S B C r := by
  apply LinearMap.ext_on (exteriorPower.ιMulti_span B r (KaehlerDifferential A B))
  rintro _ ⟨v, rfl⟩
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    exteriorDifferentialMap, exteriorScalarMap_wedge]
  congr 1
  funext i
  exact differential_map_fiber_tower A B B' S C (v i)

lemma pluricanonical_map_tower
    (R B B' K : Type*) [CommRing R] [CommRing B] [CommRing B'] [CommRing K]
    [Algebra R B] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']
    [Algebra R K] [Algebra B K] [Algebra B' K]
    [IsScalarTower R B K] [IsScalarTower R B' K] [IsScalarTower B B' K]
    (n m : ℕ) :
    ((pluricanonicalMap R R B' K n m).restrictScalars B).comp
      (pluricanonicalMap R R B B' n m) = pluricanonicalMap R R B K n m := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change pluricanonicalMap R R B' K n m
      (pluricanonicalMap R R B B' n m (PiTensorProduct.tprod B v)) =
    pluricanonicalMap R R B K n m (PiTensorProduct.tprod B v)
  simp only [pluricanonicalMap, tensorScalarMap, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.coe_restrictScalars]
  congr 1
  funext i
  exact LinearMap.congr_fun (exterior_map_fiber_tower R B B' R K n) (v i)

 

theorem rationalLattice_formallyEtale
    (R A B K : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing K]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A K] [Algebra B K] [Algebra R K]
    [IsScalarTower A B K] [IsScalarTower R A K] [IsScalarTower R B K]
    [Algebra.FormallyEtale A B] (n m : ℕ) :
    rationalLattice R B K n m =
      Submodule.span B (rationalLattice R A K n m : Set (Pluricanonical R K n m)) := by
  rw [← range_pluricanonicalMap R B K n m, ← range_pluricanonicalMap R A K n m,
    LinearMap.range_eq_map]
  rw [← formallyEtale_pluricanonical_span R A B n m, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    refine ⟨u, ?_⟩
    exact (LinearMap.congr_fun (pluricanonical_map_tower R A B K n m) u).symm
  · rintro ⟨u, rfl⟩
    refine ⟨_, ⟨u, rfl⟩, ?_⟩
    exact LinearMap.congr_fun (pluricanonical_map_tower R A B K n m) u

end ReverseLogKodaira.DifferentialBaseChange

end

end OAI

-- ---- platform node ----
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.DifferentialBaseChange
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem solution
    (R A B K : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing K]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A K] [Algebra B K] [Algebra R K]
    [IsScalarTower A B K] [IsScalarTower R A K] [IsScalarTower R B K]
    [Algebra.FormallyEtale A B] (n m : ℕ) :
    rationalLattice R B K n m =
      Submodule.span B (rationalLattice R A K n m : Set (Pluricanonical R K n m)) := by
  first
    | exact OAI.ReverseLogKodaira.DifferentialBaseChange.rationalLattice_formallyEtale R A B K n m
    | exact OAI.ReverseLogKodaira.DifferentialBaseChange.rationalLattice_formallyEtale
    | (apply OAI.ReverseLogKodaira.DifferentialBaseChange.rationalLattice_formallyEtale <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.DifferentialBaseChange.rationalLattice_formallyEtale <;> assumption)
