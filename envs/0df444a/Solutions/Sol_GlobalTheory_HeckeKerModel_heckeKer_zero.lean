-- Prove2me | solution 1 for GlobalTheory.HeckeKerModel.heckeKer_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:46:14.046801+00:00
-- url     : https://prove2.me/submissions/85d30324-552e-4ecd-a485-d86d759a49b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsTateIsoHeckeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_HeckeKerZero
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_ext
import Theorems.Thm_GlobalTheory_HeckeTate_ev_nsmul
import Theorems.Thm_GlobalTheory_LiftsToDetOne_mul
import Theorems.Thm_GlobalTheory_LiftsToSymplectic_mul
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_datum_finrank_int
import Theorems.Thm_GlobalTheory_datum_free_int
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_symplecticGroupMap
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HeckeKerModel
open GlobalTheory.HeckeTate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}
namespace GlobalTheory.HeckeKerModel
theorem _root_.solution {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {s : S ⟶ Sp B}
    (o : Obj D l b s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k) (hx : x ≫ s = spMap β)
    (P : Ideal (𝓞 E)) (p : ℕ) (hp : 0 < p) :
    o.t.HeckeKer (Over.mk x) D P p 0 (torsSub o.t (Over.mk x) p) := by
  obtain ⟨-, I, -⟩ := o.geom k x β hx
  have hmem : ∀ z, z ∈ torsSub o.t (Over.mk x) p ↔ z ^ p = 1 := fun z => mem_tors_span o.t z p
  have hset : (torsSub o.t (Over.mk x) p : Set _) = o.t.tors (Over.mk x) (Ideal.span {(p : 𝓞 E)}) :=
    rfl
  have hq : 0 < p * p := Nat.mul_pos hp hp
  refine ⟨fun z hz a => ?_, fun J hJ z hz => ?_, fun z hz a ha => ?_, fun z hz w hw => ?_, ?_, ?_⟩
  · have := o.t.act.hom a
    rw [hmem] at hz ⊢
    rw [← comp_act_natCast, Category.assoc, ← o.t.act.mul, _root_.mul_comm, o.t.act.mul, ← Category.assoc,
      comp_act_natCast, hz]
    simp
  · rw [hset]
    exact fun a ha => hz a (Ideal.mul_le_left (I := J) (J := P) (by rw [hJ]; exact ha))
  · rw [hset] at hz
    exact hz a (Ideal.mul_le_left ha)
  · obtain ⟨a, rfl⟩ := (I.onto p hp z).1 ((hmem z).1 hz)
    obtain ⟨c, rfl⟩ := (I.onto p hp w).1 ((hmem w).1 hw)
    have h := I.isom (p * p) hq (p • a) (p • c)
    rw [ev_nsmul, ev_nsmul, I.tower p p hp hp, I.tower p p hp hp] at h
    have h2 : I.ζ (p * p) ^ D.EF (p • a) (p • c) = 1 := by
      rw [((I.ζ_prim _ hq).zpow_eq_one_iff_dvd _)]
      refine ⟨D.EF a c, ?_⟩
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      push_cast
      ring
    rw [h2] at h
    have h3 : unitOn (1 : kˣ) = 1 := map_one _
    rw [h3] at h
    rw [sq]
    exact_mod_cast h
  · have := D.fin
    have := D.proj
    have := datum_free_int D
    have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
    rw [← datum_finrank_int, ← AddSubgroup.index_range_nsmul]
    have hker : (evHom I p).ker = (nsmulAddMonoidHom (α := D.La) p).range := by
      ext a
      exact (I.ker p hp a).trans ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
    rw [← hker, AddSubgroup.index_ker]
    refine Nat.card_congr ⟨fun z => ⟨Additive.ofMul z.1, ?_⟩, fun z => ⟨z.1.toMul, ?_⟩, fun _ => rfl, fun _ => rfl⟩
    · obtain ⟨a, ha⟩ := (I.onto p hp z.1).1 ((hmem _).1 z.2)
      exact ⟨a, congrArg Additive.ofMul ha⟩
    · obtain ⟨a, ha⟩ := z.2
      exact (hmem _).2 ((I.onto p hp _).2 ⟨a, congrArg Additive.toMul ha⟩)
  · rw [hset, Set.inter_self, pow_zero, _root_.mul_one]
end GlobalTheory.HeckeKerModel
