-- Prove2me | solution 1 for OAI.Lech.dutta_dimension_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T20:49:36.207395+00:00
-- url     : https://prove2.me/submissions/c5b558b3-e6b3-4ad4-b7ea-e4cb6d7c5e20

import Mathlib
import Definitions.Def_DuttaDomain
section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter IsLocalRing
open scoped Topology
namespace Lech
universe u
variable {D : Type u} [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]

noncomputable def dzExtBasis {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) {ι : Type u} (b : Module.Basis ι R M) :
    Module.Basis ι S ((ModuleCat.extendScalars f).obj M) :=
  letI := f.toAlgebra
  Algebra.TensorProduct.basis S b

omit [IsDomain D] in
lemma dz_krull (hd : dimension D = 0) : ringKrullDim D = 0 := by
  obtain ⟨k, hk⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := D))
  have htop : k ≠ ⊤ := by
    intro h; apply ringKrullDim_ne_top (R := D); rw [← hk, h]; rfl
  lift k to ℕ using htop
  have : dimension D = k := by
    simp [dimension, ← hk]
  rw [← hk]; rw [hd] at this; subst this; rfl

lemma dz_field (hd : dimension D = 0) : IsField D := by
  have : Ring.KrullDimLE 0 D := by
    rw [Ring.krullDimLE_iff, dz_krull hd]; rfl
  exact Ring.KrullDimLE.isField_of_isDomain

lemma dz_lenself (hd : dimension D = 0) : Module.length D D = 1 := by
  letI := (dz_field hd).toField
  rw [Module.length_eq_finrank D D, Module.finrank_self]; rfl

/-- homology at 0 iso to X 0 -/
noncomputable def dzHomIso (G : CochainComplex (ModuleCat.{u} D) ℤ)
    (h1 : IsZero (G.X (-1))) (h2 : IsZero (G.X 1)) : G.homology 0 ≅ G.X 0 :=
  (G.isoHomologyπ (-1) 0 (by simp) (h1.eq_of_src _ _)).symm ≪≫
    G.iCyclesIso 0 1 (by simp) (h2.eq_of_tgt _ _)

lemma dz_length_hom (G : CochainComplex (ModuleCat.{u} D) ℤ)
    (h1 : IsZero (G.X (-1))) (h2 : IsZero (G.X 1)) :
    Module.length D (G.homology 0) = Module.length D (G.X 0) :=
  (dzHomIso G h1 h2).toLinearEquiv.length_eq

lemma dz_shortEuler (hd : dimension D = 0) (G : CochainComplex (ModuleCat.{u} D) ℤ)
    (h1 : IsZero (G.X (-1))) (h2 : IsZero (G.X 1))
    [Module.Free D (G.X 0)] [Module.Finite D (G.X 0)] :
    shortEuler D G = (Module.finrank D (G.X 0) : ℝ) := by
  have := dz_length_hom G h1 h2
  rw [Module.length_of_free_of_finite (R := D) (M := (G.X 0 : Type u)), dz_lenself hd, mul_one] at this
  simp [shortEuler, hd, this]

theorem dutta_dimension_zero (p : ℕ) [Fact p.Prime] [CharP D p]
    (hd : dimension D=0) (F : CochainComplex (ModuleCat.{u} D) ℤ)
    (hF : IsShortComplex D F) :
    Tendsto (duttaSequence D p F) atTop (𝓝 (duttaMultiplicity D p F)) ∧
    multiplicity D ≤ duttaMultiplicity D p F := by
  have hb : ∀ i : ℤ, i ≠ 0 → IsZero (F.X i) := by
    intro i hi
    apply hF.bounded
    rw [hd]; omega
  have hfree := hF.term_free 0
  have hfin := hF.term_finite 0
  set r := Module.finrank D (F.X 0) with hr
  have hseq : duttaSequence D p F = fun _ => (r : ℝ) := by
    funext n
    let f := iterateFrobenius D p n
    let b := Module.Free.chooseBasis D (F.X 0)
    let b' := dzExtBasis f (F.X 0) b
    have e1 : ∀ i : ℤ, i ≠ 0 → IsZero ((frobeniusComplex D p n F).X i) := fun i hi =>
      (ModuleCat.extendScalars f).map_isZero (hb i hi)
    haveI : Module.Free D ((frobeniusComplex D p n F).X 0) := Module.Free.of_basis b'
    haveI : Module.Finite D ((frobeniusComplex D p n F).X 0) := Module.Finite.of_basis b'
    rw [duttaSequence, dz_shortEuler hd _ (e1 _ (by norm_num)) (e1 _ (by norm_num)), hd]
    simp only [Nat.cast_zero, mul_zero, neg_zero, zpow_zero, one_mul]
    rw [show Module.finrank D ((frobeniusComplex D p n F).X 0) = Fintype.card _ from
      Module.finrank_eq_card_basis b', hr, Module.finrank_eq_card_basis b]
  have hmult : duttaMultiplicity D p F = r := by
    rw [duttaMultiplicity, hseq]; exact tendsto_const_nhds.limUnder_eq
  refine ⟨by rw [hseq, hmult]; exact tendsto_const_nhds, ?_⟩
  -- multiplicity = 1
  have hm : maximalIdeal D = ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq).mp (dz_field hd)
  have hnc : ∀ N : ℕ, 1 ≤ N → normalizedColength D N = 1 := by
    intro N hN
    have : maximalIdeal D ^ N = ⊥ := by
      rw [hm]; obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hN
      rw [pow_succ, Ideal.mul_bot]
    have hl : Module.length D (D ⧸ maximalIdeal D ^ N) = 1 := by
      rw [this, ← dz_lenself hd]
      exact (Submodule.quotEquivOfEqBot (⊥ : Ideal D) rfl).length_eq
    simp [normalizedColength, colength, hd, hl]
  have hmul : multiplicity D = 1 := by
    rw [multiplicity]
    apply Tendsto.limUnder_eq
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (hnc N hN).symm
  rw [hmul, hmult]
  -- r ≥ 1
  have hnt : Nontrivial (F.X 0) := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    apply hF.homology_zero_nonzero
    exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
      (dzHomIso F (hb _ (by norm_num)) (hb _ (by norm_num)))
  have : 0 < r := Module.finrank_pos
  exact_mod_cast this
end Lech

end

end OAI
end

universe v

theorem solution {D : Type v} [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
    (p : ℕ) [Fact p.Prime] [CharP D p]
    (hd : OAI.Lech.dimension D = 0) (F : CochainComplex (ModuleCat.{v} D) ℤ)
    (hF : OAI.Lech.IsShortComplex D F) :
    Filter.Tendsto (OAI.Lech.duttaSequence D p F) Filter.atTop (nhds (OAI.Lech.duttaMultiplicity D p F)) ∧
    OAI.Lech.multiplicity D ≤ OAI.Lech.duttaMultiplicity D p F :=
  OAI.Lech.dutta_dimension_zero p hd F hF
