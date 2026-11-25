-- Prove2me | solution 1 for GlobalTheory.FinOf.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:18:47.245532+00:00
-- url     : https://prove2.me/submissions/bf31c358-1cc0-4324-8b58-e9fb5ee82daa

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinOfLocalAlgebraMap
import Theorems.Thm_GlobalTheory_FinOf_finOf_split
import Theorems.Thm_GlobalTheory_FinOf_finOf_unram
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FinOf
variable {R₀ : Type} [CommRing R₀]
namespace GlobalTheory.FinOf
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (p : ℕ), IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left → Smooth G.hom →
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra (O : Type) A) (_ : Algebra R₀ A) (_ : IsScalarTower R₀ (O : Type) A),
      Module.Free (O : Type) A ∧ Module.Finite (O : Type) A ∧ ∃ y : sp (R₀ := R₀) A ⟶ G, y ^ p = 1 ∧
      ∀ (S : Type) [CommRing S] [Algebra (O : Type) S] [Algebra R₀ S] [IsScalarTower R₀ (O : Type) S] (z : sp (R₀ := R₀) S ⟶ G), z ^ p = 1 →
        ∃! φ : A →ₐ[(O : Type)] S, spMap (φ.restrictScalars R₀) ≫ y = z) →
  (∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Finite (A →ₐ[O] O)],
    (∀ f : A, (∀ φ : A →ₐ[O] O, φ f = 0) → f = 0) →
    ∃ (n : ℕ) (ε : Fin n → A), CompleteOrthogonalIdempotents ε ∧ ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - ε i})) →
  (∀ (C O A : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [CommRing A] [Algebra O A] [Module.Free O A] [Module.Finite O A],
    (∀ φ φ' : A →ₐ[O] DualNumber C, (∀ a, (φ a).fst = (φ' a).fst) → φ = φ') →
    Finite (A →ₐ[O] O) ∧ (∀ f : A, (∀ φ : A →ₐ[O] O, φ f = 0) → f = 0) ∧ Module.finrank O A = Nat.card (A →ₐ[O] O)) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (p : ℕ) (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left → Smooth G.hom →
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) [Algebra (O : Type) C], v.Integers (O : Type) → p ≠ 0 →
    Nonempty (FIN B O p)) := by
  intro REP SPLIT ETA R₀ _ G _ _ O p B e hbij hadd hnat hfin hflat hsm C _ _ _ v _ hv hp
  obtain ⟨A, _, _, _, _, hAfree, hAfin, y, hy, huniv⟩ := REP G O p hfin hflat hsm
  have he0 : ∀ R, e R 0 = 1 := fun R => by
    have h := hadd R 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hen : ∀ R (x : B.G R) (n : ℕ), e R (n • x) = e R x ^ n := fun R x n => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, he0]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have htor : ∀ R (x : B.G R), p • x = 0 ↔ e R x ^ p = 1 := fun R x => by
    rw [← hen, ← he0 R, (hbij R).1.eq_iff]
  let pt : ∀ S : LAlg R₀, (A →ₐ[R₀] S) → B.G S := fun S φ =>
    (Equiv.ofBijective _ (hbij S)).symm (spMap φ ≫ y)
  have hpt : ∀ S φ, e S (pt S φ) = spMap φ ≫ y := fun S φ =>
    (Equiv.ofBijective _ (hbij S)).apply_symm_apply _
  have pt_nat : ∀ {S S' : LAlg R₀} (f : LHom S S') (φ : A →ₐ[R₀] S),
      B.map f (pt S φ) = pt S' (f.1.comp φ) := fun {S S'} f φ => (hbij S').1 (by
    rw [hnat, hpt, hpt, ← Category.assoc, spMap_comp])
  have pt_p : ∀ S φ, p • pt S φ = 0 := fun S φ => by
    rw [htor, hpt, ← MonObj.comp_pow, hy, MonObj.comp_one]
  have pt_univ : ∀ (S : LAlg R₀) (s : O →ₐ[R₀] S) (z : B.G S), p • z = 0 →
      ∃! φ : A →ₐ[R₀] S, φ.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) = s ∧ pt S φ = z := by
    intro S s z hz
    letI : Algebra (O : Type) S := s.toRingHom.toAlgebra
    haveI : IsScalarTower R₀ (O : Type) S :=
      IsScalarTower.of_algebraMap_eq fun r => (s.commutes r).symm
    obtain ⟨φ, hφ, hu⟩ := huniv S (e S z) ((htor S z).1 hz)
    refine ⟨φ.restrictScalars R₀, ⟨by ext r; exact φ.commutes r, (hbij S).1 (by rw [hpt, hφ])⟩,
      fun φ' ⟨h1, h2⟩ => ?_⟩
    have h3 := hu ⟨φ'.toRingHom, fun r => AlgHom.congr_fun h1 r⟩ (by rw [← h2, hpt]; rfl)
    rw [← h3]; rfl
  letI : Algebra R₀ C := ((algebraMap (O : Type) C).comp (algebraMap R₀ (O : Type))).toAlgebra
  haveI : IsScalarTower R₀ (O : Type) C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hfinite, hsep, hrank⟩ := ETA C O A v hv
    (finOf_unram O B p hp pt pt_nat pt_p pt_univ C)
  obtain ⟨n, ε, hε, hloc⟩ := SPLIT O A hsep
  exact finOf_split O B p pt pt_nat pt_p pt_univ hsep hrank ε hε
end GlobalTheory.FinOf
