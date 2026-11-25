-- Prove2me | solution 1 for GlobalTheory.ChLaw.groupLaw_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:02:07.05194+00:00
-- url     : https://prove2.me/submissions/65ee0a08-48b4-4112-903d-07d4a00073cb

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GroupLawPowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChLaw
private lemma nil_of_mem_span {S : Type} [CommRing S] {s : Set S} (hs : ∀ a ∈ s, IsNilpotent a)
    {c : S} (hc : c ∈ Ideal.span s) : IsNilpotent c := by
  have h : Ideal.span s ≤ nilradical S := Ideal.span_le.2 fun a ha => mem_nilradical.2 (hs a ha)
  exact mem_nilradical.1 (h hc)
end GlobalTheory.ChLaw
end

set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChLaw
namespace GlobalTheory.ChLaw
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (c : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (κ → S) → S),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : κ → S),
      (∀ i, IsNilpotent (a i)) → φ (c S a) = c S' (fun i => φ (a i))) →
    ∃ f : MvPowerSeries κ R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (∀ i, IsNilpotent (a i)) → c S a = nEval f a) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (g : ℕ) (x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)),
    ((∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : Fin g → S),
        (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i))) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
        (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)) →
    ∃ F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) →
      (∀ k, fAdd F a b k ∈ Ideal.span (Set.range a ∪ Set.range b)) ∧ x S a * x S b = x S (fAdd F a b)) := by
  classical
  intro _ h2 R₀ _ G _ _ g x ⟨h0, hnat, hinj, hsur⟩
  have hex : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → ∃ c : Fin g → S,
        (∀ k, c k ∈ Ideal.span (Set.range a ∪ Set.range b)) ∧ (∀ k, IsNilpotent (c k)) ∧
        x S a * x S b = x S c := by
    intro S _ _ a b ha hb
    set I : Ideal S := Ideal.span (Set.range a ∪ Set.range b) with hI
    have hnil : ∀ c ∈ I, IsNilpotent c := fun c hc =>
      nil_of_mem_span (by rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩); exacts [ha i, hb i]) hc
    have hker : ∀ c, c ∈ RingHom.ker (Ideal.Quotient.mkₐ R₀ I) ↔ c ∈ I := fun c => by
      rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    have hz : spMap (Ideal.Quotient.mkₐ R₀ I) ≫ (x S a * x S b) = 1 := by
      have ea : (fun i => Ideal.Quotient.mkₐ R₀ I (a i)) = 0 := funext fun i =>
        (hker _).2 (Ideal.subset_span (Or.inl ⟨i, rfl⟩))
      have eb : (fun i => Ideal.Quotient.mkₐ R₀ I (b i)) = 0 := funext fun i =>
        (hker _).2 (Ideal.subset_span (Or.inr ⟨i, rfl⟩))
      rw [MonObj.comp_mul, hnat _ _ _ a ha, hnat _ _ _ b hb, ea, eb, h0, _root_.mul_one]
    obtain ⟨c, hc, hzc⟩ := hsur S (S ⧸ I) (Ideal.Quotient.mkₐ R₀ I)
      (Ideal.Quotient.mkₐ_surjective R₀ I) (fun c hc => hnil c ((hker c).1 hc)) _ hz
    exact ⟨c, fun k => (hker _).1 (hc k), fun k => hnil _ ((hker _).1 (hc k)), hzc⟩
  choose cc hc1 hc2 hc3 using hex
  have hF : ∀ k : Fin g, ∃ f : MvPowerSeries (Fin g ⊕ Fin g) R₀,
      ∀ (S : Type) [CommRing S] [Algebra R₀ S] (u : Fin g ⊕ Fin g → S)
        (hu : ∀ i, IsNilpotent (u i)),
        cc S (fun i => u (Sum.inl i)) (fun i => u (Sum.inr i)) (fun _ => hu _) (fun _ => hu _) k =
          nEval f u := by
    intro k
    obtain ⟨f, hf⟩ := h2 (R₀ := R₀) (κ := Fin g ⊕ Fin g)
      (fun S _ _ u => if hu : ∀ i, IsNilpotent (u i) then
        cc S (fun i => u (Sum.inl i)) (fun i => u (Sum.inr i)) (fun _ => hu _) (fun _ => hu _) k
        else 0) (by
        intro S _ _ S' _ _ φ u hu
        have hu' : ∀ i, IsNilpotent (φ (u i)) := fun i => (hu i).map φ
        simp only [dif_pos hu, dif_pos hu']
        have := hinj S'
          (fun j => φ (cc S (fun i => u (Sum.inl i)) (fun i => u (Sum.inr i))
            (fun _ => hu _) (fun _ => hu _) j))
          (cc S' (fun i => φ (u (Sum.inl i))) (fun i => φ (u (Sum.inr i)))
            (fun _ => hu' _) (fun _ => hu' _))
          (fun j => (hc2 _ _ _ _ _ j).map φ) (hc2 _ _ _ _ _) (by
            rw [← hnat _ _ φ _ (hc2 _ _ _ _ _), ← hc3, ← hc3, MonObj.comp_mul,
              hnat _ _ φ _ (fun _ => hu _), hnat _ _ φ _ (fun _ => hu _)])
        exact congrFun this k)
    refine ⟨f, fun S _ _ u hu => ?_⟩
    have := hf S u hu
    simpa only [dif_pos hu] using this
  choose F hF using hF
  refine ⟨F, fun S _ _ a b ha hb => ?_⟩
  have e : fAdd F a b = cc S a b ha hb := by
    funext k
    have hu : ∀ i, IsNilpotent (Sum.elim a b i) := by
      rintro (i | i); exacts [ha i, hb i]
    exact (hF k S (Sum.elim a b) hu).symm
  rw [e]
  exact ⟨hc1 S a b ha hb, hc3 S a b ha hb⟩
end GlobalTheory.ChLaw
