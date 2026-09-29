-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_pullback_iso_pullback_of_comp_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ae2369c1-9a85-5296-807a-b5a7e45811fd

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pullback_iso_pullback_of_comp_eq_one_iff

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace TorsorIsoGC5

variable {k : Type u} [CommRing k]

theorem map_one {G Q : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} {fQ : Q ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f) (LQ : RelativeGroupLaw k fQ) (q : SchemeHomOver f fQ)
    (hq : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
        LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    NeronModelInfra.schemeHomOverComp (L.one t) q = LQ.one t := by
  letI := LQ.pointGroup t
  have h : NeronModelInfra.schemeHomOverComp (L.one t) q * NeronModelInfra.schemeHomOverComp (L.one t) q =
      NeronModelInfra.schemeHomOverComp (L.one t) q := by
    show LQ.mul t _ _ = _
    rw [← hq, L.one_mul]
  exact mul_eq_right.mp h

theorem map_inv {G Q : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} {fQ : Q ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f) (LQ : RelativeGroupLaw k fQ) (q : SchemeHomOver f fQ)
    (hq : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
        LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (L.inv t x) q = LQ.inv t (NeronModelInfra.schemeHomOverComp x q) := by
  letI := LQ.pointGroup t
  have h : NeronModelInfra.schemeHomOverComp (L.inv t x) q * NeronModelInfra.schemeHomOverComp x q = 1 := by
    show LQ.mul t _ _ = LQ.one t
    rw [← hq, L.inv_mul_cancel, map_one L LQ q hq]
  exact eq_inv_of_mul_eq_one_left h

theorem inv_natural {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (t' : T' ⟶ Spec (CommRingCat.of k))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) =
      L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) * GoodReductionJacobian.schemeHomOverComp ψ hψ x = 1 := by
    show L.mul t' _ _ = L.one t'
    rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]
  exact eq_inv_of_mul_eq_one_left h

end TorsorIsoGC5

theorem solution
    (k : Type u) [CommRing k]
    {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i]
    {Q : Scheme.{u}} (fQ : Q ⟶ Spec (CommRingCat.of k)) (LQ : RelativeGroupLaw k fQ)
    (q : SchemeHomOver f fQ)
    (hq : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
        LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp x q = LQ.one t ↔
        ∃ y : SchemeHomOver t (i ≫ f),
          NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x) :
    ∃ e : pullback q.1 q.1 ≅ pullback (i ≫ f) f, e.hom ≫ pullback.snd (i ≫ f) f = pullback.snd q.1 q.1 := by
  classical

  let t : pullback q.1 q.1 ⟶ Spec (CommRingCat.of k) := pullback.snd q.1 q.1 ≫ f
  have hfst : pullback.fst q.1 q.1 ≫ f = t := by
    show _ = pullback.snd q.1 q.1 ≫ f
    calc pullback.fst q.1 q.1 ≫ f = (pullback.fst q.1 q.1 ≫ q.1) ≫ fQ := by rw [Category.assoc, q.2]
      _ = (pullback.snd q.1 q.1 ≫ q.1) ≫ fQ := by rw [pullback.condition]
      _ = pullback.snd q.1 q.1 ≫ f := by rw [Category.assoc, q.2]
  let x : SchemeHomOver t f := ⟨pullback.fst q.1 q.1, hfst⟩
  let y : SchemeHomOver t f := ⟨pullback.snd q.1 q.1, rfl⟩
  have hxy : NeronModelInfra.schemeHomOverComp x q = NeronModelInfra.schemeHomOverComp y q :=
    Subtype.ext pullback.condition

  let z : SchemeHomOver t f := L.mul t x (L.inv t y)
  have hz : NeronModelInfra.schemeHomOverComp z q = LQ.one t := by
    letI := LQ.pointGroup t
    show NeronModelInfra.schemeHomOverComp (L.mul t x (L.inv t y)) q = 1
    rw [hq, TorsorIsoGC5.map_inv L LQ q hq, hxy]
    exact mul_inv_cancel _
  obtain ⟨n, hn⟩ := (hker t z).mp hz
  have hn1 : n.1 ≫ i = z.1 := congrArg Subtype.val hn

  let t' : pullback (i ≫ f) f ⟶ Spec (CommRingCat.of k) := pullback.snd (i ≫ f) f ≫ f
  let n' : SchemeHomOver t' (i ≫ f) := ⟨pullback.fst (i ≫ f) f, pullback.condition⟩
  let y' : SchemeHomOver t' f := ⟨pullback.snd (i ≫ f) f, rfl⟩
  let in' : SchemeHomOver t' f := NeronModelInfra.schemeHomOverComp n' (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)
  have hin' : NeronModelInfra.schemeHomOverComp in' q = LQ.one t' := (hker t' in').mpr ⟨n', rfl⟩
  let w : SchemeHomOver t' f := L.mul t' in' y'
  have hw : w.1 ≫ q.1 = y'.1 ≫ q.1 := by
    have := hq t' in' y'
    rw [hin', LQ.one_mul] at this
    exact congrArg Subtype.val this

  let φ : pullback q.1 q.1 ⟶ pullback (i ≫ f) f :=
    pullback.lift n.1 (pullback.snd q.1 q.1) (by rw [n.2])
  let ψ : pullback (i ≫ f) f ⟶ pullback q.1 q.1 := pullback.lift w.1 y'.1 hw
  have hφ : φ ≫ t' = t := by show φ ≫ pullback.snd _ _ ≫ f = _; rw [pullback.lift_snd_assoc]
  have hψ : ψ ≫ t = t' := by show ψ ≫ pullback.snd _ _ ≫ f = _; rw [pullback.lift_snd_assoc]

  have hφin : GoodReductionJacobian.schemeHomOverComp φ hφ in' = z :=
    Subtype.ext (by simp only [GoodReductionJacobian.schemeHomOverComp_coe, in', NeronModelInfra.schemeHomOverComp_coe,
      n', φ, pullback.lift_fst_assoc, hn1])
  have hφy : GoodReductionJacobian.schemeHomOverComp φ hφ y' = y :=
    Subtype.ext (by simp only [GoodReductionJacobian.schemeHomOverComp_coe, y', y, φ, pullback.lift_snd])
  have hψx : GoodReductionJacobian.schemeHomOverComp ψ hψ x = w :=
    Subtype.ext (by simp only [GoodReductionJacobian.schemeHomOverComp_coe, x, ψ, pullback.lift_fst])
  have hψy : GoodReductionJacobian.schemeHomOverComp ψ hψ y = y' :=
    Subtype.ext (by simp only [GoodReductionJacobian.schemeHomOverComp_coe, y, y', ψ, pullback.lift_snd])
  refine ⟨⟨φ, ψ, ?_, ?_⟩, pullback.lift_snd _ _ _⟩
  ·
    apply pullback.hom_ext
    · rw [Category.assoc, Category.id_comp]
      show φ ≫ ψ ≫ pullback.fst q.1 q.1 = x.1
      rw [pullback.lift_fst]
      have : GoodReductionJacobian.schemeHomOverComp φ hφ w = x := by
        show GoodReductionJacobian.schemeHomOverComp φ hφ (L.mul t' in' y') = x
        rw [L.mul_natural, hφin, hφy]
        show L.mul t (L.mul t x (L.inv t y)) y = x
        rw [L.mul_assoc, L.inv_mul_cancel, L.mul_one]
      exact congrArg Subtype.val this
    · rw [Category.assoc, Category.id_comp]
      show φ ≫ ψ ≫ pullback.snd q.1 q.1 = pullback.snd q.1 q.1
      rw [pullback.lift_snd, pullback.lift_snd]
  ·
    apply pullback.hom_ext
    · rw [Category.assoc, Category.id_comp]
      show ψ ≫ φ ≫ pullback.fst (i ≫ f) f = pullback.fst (i ≫ f) f
      rw [pullback.lift_fst, ← cancel_mono i, Category.assoc, hn1]
      have : GoodReductionJacobian.schemeHomOverComp ψ hψ z = in' := by
        show GoodReductionJacobian.schemeHomOverComp ψ hψ (L.mul t x (L.inv t y)) = in'
        rw [L.mul_natural, TorsorIsoGC5.inv_natural, hψx, hψy]
        show L.mul t' (L.mul t' in' y') (L.inv t' y') = in'
        rw [L.mul_assoc, L.mul_inv_cancel, L.mul_one]
      exact congrArg Subtype.val this
    · rw [Category.assoc, Category.id_comp]
      show ψ ≫ φ ≫ pullback.snd (i ≫ f) f = pullback.snd (i ≫ f) f
      rw [pullback.lift_snd, pullback.lift_snd]

end S_GoodReductionJacobian_RelativeGroupLaw_exists_pullback_iso_pullback_of_comp_eq_one_iff
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pullback_iso_pullback_of_comp_eq_one_iff (solution)
