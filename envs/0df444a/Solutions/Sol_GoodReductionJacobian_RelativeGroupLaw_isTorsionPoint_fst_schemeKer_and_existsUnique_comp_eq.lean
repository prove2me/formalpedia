-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isTorsionPoint_fst_schemeKer_and_existsUnique_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/58bc81a6-10af-5a2e-a917-076be85f1985

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isTorsionPoint_fst_schemeKer_and_existsUnique_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace C6KerRepr

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem nsmul_val {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    (L.nsmul t n x).1 = x.1 ≫ L.schemeNsmul n := by
  have h := L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x := Subtype.ext (Category.comp_id _)
  rw [hx] at h
  rw [← h]
  rfl

theorem one_val {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h := L.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t)
  rw [← h]
  rfl

theorem isTorsionPoint_iff_comp {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    L.IsTorsionPoint t n x ↔ x.1 ≫ L.schemeNsmul n = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  rw [L.isTorsionPoint_def, ← nsmul_val L, ← one_val L]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

noncomputable def kerPoint (n : ℕ) : SchemeHomOver (L.schemeKerStr n) f :=
  ⟨pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1, by
    have e2 := (L.one (𝟙 (Spec (CommRingCat.of R)))).2
    calc pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f
        = pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ (L.schemeNsmul n ≫ f) := by
          rw [L.schemeNsmul_over n]
      _ = (pullback.snd (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫
            (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫ f := by
          rw [← Category.assoc, pullback.condition]
      _ = L.schemeKerStr n := by
          rw [Category.assoc, e2, Category.comp_id]⟩

@[scoped simp] theorem kerPoint_coe (n : ℕ) :
    (kerPoint L n).1 = pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := rfl

theorem isTorsionPoint_kerPoint (n : ℕ) : L.IsTorsionPoint (L.schemeKerStr n) n (kerPoint L n) := by
  rw [isTorsionPoint_iff_comp]
  exact pullback.condition

theorem existsUnique_comp_kerPoint (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z : SchemeHomOver t f) (hz : L.IsTorsionPoint t n z) :
    ∃! g : T ⟶ L.schemeKer n, g ≫ (kerPoint L n).1 = z.1 := by
  rw [isTorsionPoint_iff_comp] at hz
  refine ⟨pullback.lift z.1 t hz, pullback.lift_fst _ _ _, fun g hg => ?_⟩
  apply pullback.hom_ext
  · rw [pullback.lift_fst]; exact hg
  · rw [pullback.lift_snd]

    have e2 := (L.one (𝟙 (Spec (CommRingCat.of R)))).2
    have h1 : (g ≫ pullback.snd _ _) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 =
        t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc]
      change (g ≫ (kerPoint L n).1) ≫ L.schemeNsmul n = _
      rw [hg, hz]
    have h2 := congrArg (fun k => k ≫ f) h1
    simp only [Category.assoc, e2, Category.comp_id] at h2
    exact h2

end C6KerRepr
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isTorsionPoint_fst_schemeKer_and_existsUnique_comp_eq.C6KerRepr"

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (n : ℕ) :
    ∃ hu : pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f = L.schemeKerStr n,
      L.IsTorsionPoint (L.schemeKerStr n) n ⟨pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1, hu⟩ ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (z : SchemeHomOver t f), L.IsTorsionPoint t n z →
        ∃! g : T ⟶ L.schemeKer n, g ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 = z.1 :=
  ⟨(C6KerRepr.kerPoint L n).2, C6KerRepr.isTorsionPoint_kerPoint L n,
    fun t z hz => C6KerRepr.existsUnique_comp_kerPoint L n t z hz⟩

end S_GoodReductionJacobian_RelativeGroupLaw_isTorsionPoint_fst_schemeKer_and_existsUnique_comp_eq
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isTorsionPoint_fst_schemeKer_and_existsUnique_comp_eq (solution)
