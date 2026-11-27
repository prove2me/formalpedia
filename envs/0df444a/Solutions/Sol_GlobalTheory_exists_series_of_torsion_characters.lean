-- Prove2me | solution 1 for GlobalTheory.exists_series_of_torsion_characters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:47:23.502333+00:00
-- url     : https://prove2.me/submissions/c761dc1a-a29f-4fd3-9e3f-9970d3e22485

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSeriesOfTorsionCharacters
import Theorems.Thm_GlobalTheory_CharGerm_exists_series
import Theorems.Thm_GlobalTheory_CharGerm_exists_pow_eq_one
import Theorems.Thm_GlobalTheory_CharGerm_unitOf_eq_val
import Theorems.Thm_GlobalTheory_CharGerm_map_val
import Theorems.Thm_GlobalTheory_CharGerm_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (c : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (κ → S) → S),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : κ → S),
      (∀ i, IsNilpotent (a i)) → φ (c S a) = c S' (fun i => φ (a i))) →
    ∃ f : MvPowerSeries κ R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (∀ i, IsNilpotent (a i)) → c S a = nEval f a) →
  (∀ (p : ℕ) [Fact p.Prime] {R₀ : Type} [CommRing R₀] [IsAdicComplete (Ideal.span {(p : R₀)}) R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G]
    (g : ℕ) (x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)),
    ((∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : Fin g → S),
        (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i))) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
        (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)) →
    ∀ χ : ReciprocityTheory.ChartRestriction.G.Pdiv.Tv G p, ∃ s : MvPowerSeries (Fin g) R₀, MvPowerSeries.coeff 0 s = 1 ∧
      ∀ (S : Type) [CommRing S] [Algebra R₀ S], IsNilpotent (p : S) → ∀ a : Fin g → S, (∀ i, IsNilpotent (a i)) →
        (∃ N : ℕ, x S a ^ (p ^ N) = 1) ∧
        ∀ (N : ℕ) (w : sp (R₀ := R₀) S ⟶ ReciprocityTheory.ChartRestriction.G.Semi.torsion G (p ^ N)), w ≫ ReciprocityTheory.ChartRestriction.G.Semi.torsion.ι G (p ^ N) = x S a →
          (ReciprocityTheory.ChartRestriction.G.Pdiv.unitOf (O := R₀) (w ≫ χ.χ N) : S) = nEval s a) := by
  intro hE _ p _ R₀ _ _ G _ _ g x ⟨h0, hnat, hinj, hsurj⟩ χ
  obtain ⟨s, hs⟩ := CharGerm.exists_series (R₀ := R₀) (κ := Fin g) p
    (fun S _ _ a => CharGerm.val χ (x S a)) (fun S _ _ S' _ _ φ a hp ha => by
      rw [CharGerm.map_val χ φ (CharGerm.exists_pow_eq_one h0 hnat hinj hsurj p hp ha),
        hnat _ _ _ _ ha])
  have hs' : ∀ (S : Type) [CommRing S] [Algebra R₀ S], IsNilpotent (p : S) → ∀ a : Fin g → S,
      (∀ i, IsNilpotent (a i)) → CharGerm.val χ (x S a) = nEval s a := by
    intro S _ _ ⟨n, hn⟩ a ha
    choose k hk using ha
    have hN : ∀ i, a i ^ (n + Finset.univ.sup k) = 0 := fun i =>
      pow_eq_zero_of_le ((Finset.le_sup (f := k) (Finset.mem_univ i)).trans (Nat.le_add_left _ _))
        (hk i)
    rw [(hE s S a).1 _ hN]
    exact hs S a _ (pow_eq_zero_of_le (Nat.le_add_right _ _) hn) hN
  refine ⟨s, ?_, fun S _ _ hp a ha => ⟨CharGerm.exists_pow_eq_one h0 hnat hinj hsurj p hp ha,
    fun N w hw => (CharGerm.unitOf_eq_val χ w hw).trans (hs' S hp a ha)⟩⟩
  refine sub_eq_zero.mp (IsHausdorff.haus' (I := Ideal.span {(p : R₀)}) _ fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
  have hp : IsNilpotent (p : R₀ ⧸ Ideal.span {(p : R₀)} ^ n) := ⟨n, by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : R₀)} ^ n)), ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n⟩
  have h1 := hs' _ hp 0 (fun _ => IsNilpotent.zero)
  have h2 := ((hE s (R₀ ⧸ Ideal.span {(p : R₀)} ^ n) 0).2 (fun _ => IsNilpotent.zero)).2
  rw [h0, CharGerm.val_one] at h1
  have h3 : Ideal.span (Set.range (0 : Fin g → R₀ ⧸ Ideal.span {(p : R₀)} ^ n)) = ⊥ := by
    rw [Ideal.span_eq_bot]
    rintro _ ⟨i, rfl⟩
    rfl
  rw [h3, ← h1, Ideal.mem_bot, sub_eq_zero] at h2
  rw [map_one]
  exact h2.symm
end GlobalTheory
