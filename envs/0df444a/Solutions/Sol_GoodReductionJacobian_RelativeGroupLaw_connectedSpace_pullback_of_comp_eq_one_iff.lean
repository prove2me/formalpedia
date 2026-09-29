-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.connectedSpace_pullback_of_comp_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/07311ac8-7d61-56c9-a8b4-b54698e563b9

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_connectedSpace_pullback_of_comp_eq_one_iff

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace LiftConn

variable {k : Type u} [Field k]

section grp

variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))

lemma mul_inv_mul_cancel (x y : SchemeHomOver t f) :
    L.mul t x (L.mul t (L.inv t x) y) = y := by
  rw [← L.mul_assoc, L.mul_inv_cancel, L.one_mul]

lemma eq_one_of_mul_self (a : SchemeHomOver t f) (h : L.mul t a a = a) : a = L.one t := by
  calc a = L.mul t (L.one t) a := (L.one_mul t a).symm
    _ = L.mul t (L.mul t (L.inv t a) a) a := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t a) (L.mul t a a) := by rw [L.mul_assoc]
    _ = L.mul t (L.inv t a) a := by rw [h]
    _ = L.one t := L.inv_mul_cancel t a

end grp

section main

variable {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G)
  {Q : Scheme.{u}} {fQ : Q ⟶ Spec (CommRingCat.of k)} (LQ : RelativeGroupLaw k fQ)
  (q : SchemeHomOver f fQ)
  (hq : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
      LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
  (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp x q = LQ.one t ↔
      ∃ y : SchemeHomOver t (i ≫ f),
        NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x)

include hq in

lemma comp_one_eq_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    NeronModelInfra.schemeHomOverComp (L.one t) q = LQ.one t := by
  apply eq_one_of_mul_self LQ t
  rw [← hq, L.one_mul]

include hq in

lemma comp_inv_mul_eq_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t f)
    (h : NeronModelInfra.schemeHomOverComp x q = NeronModelInfra.schemeHomOverComp y q) :
    NeronModelInfra.schemeHomOverComp (L.mul t (L.inv t x) y) q = LQ.one t := by
  rw [hq, ← h, ← hq, L.inv_mul_cancel, comp_one_eq_one L LQ q hq]

include hq hker in

theorem connectedSpace_pullback [GeometricallyConnected (i ≫ f)] [Surjective q.1]
    {K : Type u} [Field K] (y : Spec (CommRingCat.of K) ⟶ Q) :
    ConnectedSpace ↑(pullback q.1 y) := by
  classical
  let F : Scheme.{u} := pullback q.1 y
  let prG : F ⟶ G := pullback.fst q.1 y
  let prK : F ⟶ Spec (CommRingCat.of K) := pullback.snd q.1 y
  have hcond : prG ≫ q.1 = prK ≫ y := pullback.condition
  have hqf : q.1 ≫ fQ = f := q.2

  obtain ⟨s0⟩ : Nonempty ↑(Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨p, -⟩ := prK.surjective s0

  let pt : Spec (F.residueField p) ⟶ F := F.fromSpecResidueField p
  let σ : Spec (F.residueField p) ⟶ Spec (CommRingCat.of k) := pt ≫ prK ≫ y ≫ fQ

  let NK : Scheme.{u} := pullback (i ≫ f) σ
  have hNK : ConnectedSpace ↑NK :=
    pullback_of_geometrically (GeometricallyConnected.geometrically_connectedSpace (f := i ≫ f))
      _ σ
  let tN : NK ⟶ Spec (CommRingCat.of k) := pullback.snd (i ≫ f) σ ≫ σ
  have hNcond : pullback.fst (i ≫ f) σ ≫ i ≫ f = pullback.snd (i ≫ f) σ ≫ σ := by
    simpa only [Category.assoc] using (pullback.condition (f := i ≫ f) (g := σ))
  let x1 : SchemeHomOver tN f :=
    ⟨pullback.snd (i ≫ f) σ ≫ pt ≫ prG, by
      simp only [tN, σ, Category.assoc, ← hqf]
      rw [reassoc_of% hcond]⟩
  let x2 : SchemeHomOver tN f := ⟨pullback.fst (i ≫ f) σ ≫ i, by
      simp only [tN, Category.assoc]; exact hNcond⟩
  have hx2 : NeronModelInfra.schemeHomOverComp x2 q = LQ.one tN := by
    refine (hker tN x2).mpr ⟨⟨pullback.fst (i ≫ f) σ, hNcond⟩, ?_⟩
    exact Subtype.ext rfl

  let θG : NK ⟶ G := (L.mul tN x1 x2).1
  have hθG : θG ≫ q.1 = (pullback.snd (i ≫ f) σ ≫ pt ≫ prK) ≫ y := by
    have h1 : θG ≫ q.1 = (NeronModelInfra.schemeHomOverComp (L.mul tN x1 x2) q).1 := rfl
    rw [h1, hq, hx2, LQ.mul_one]
    show (pullback.snd (i ≫ f) σ ≫ pt ≫ prG) ≫ q.1 = _
    simp only [Category.assoc, hcond]
  let θ : NK ⟶ F := pullback.lift θG (pullback.snd (i ≫ f) σ ≫ pt ≫ prK) hθG

  let FK : Scheme.{u} := pullback prK (pt ≫ prK)
  let π : FK ⟶ F := pullback.fst prK (pt ≫ prK)
  have hFKcond : π ≫ prK = pullback.snd prK (pt ≫ prK) ≫ pt ≫ prK := pullback.condition
  have hπ : Function.Surjective π := π.surjective
  let tF : FK ⟶ Spec (CommRingCat.of k) := π ≫ prK ≫ y ≫ fQ
  let uu : SchemeHomOver tF f := ⟨π ≫ prG, by
      simp only [tF, Category.assoc, ← hqf]
      rw [reassoc_of% hcond]⟩
  let pK : SchemeHomOver tF f := ⟨pullback.snd prK (pt ≫ prK) ≫ pt ≫ prG, by
      simp only [tF, Category.assoc, ← hqf]
      rw [reassoc_of% hcond, ← reassoc_of% hFKcond]⟩
  have hpu : NeronModelInfra.schemeHomOverComp pK q = NeronModelInfra.schemeHomOverComp uu q := by
    apply Subtype.ext
    show (pullback.snd prK (pt ≫ prK) ≫ pt ≫ prG) ≫ q.1 = (π ≫ prG) ≫ q.1
    simp only [Category.assoc, hcond]
    rw [← reassoc_of% hFKcond]
  have hx : NeronModelInfra.schemeHomOverComp (L.mul tF (L.inv tF pK) uu) q = LQ.one tF :=
    comp_inv_mul_eq_one L LQ q hq tF pK uu hpu
  obtain ⟨n, hn⟩ := (hker tF _).mp hx
  have hn1 : n.1 ≫ i = (L.mul tF (L.inv tF pK) uu).1 := congrArg Subtype.val hn
  have hψw : n.1 ≫ i ≫ f = pullback.snd prK (pt ≫ prK) ≫ σ := by
    rw [n.2]
    simp only [tF, σ]
    rw [← reassoc_of% hFKcond]
  let ψ : FK ⟶ NK := pullback.lift n.1 (pullback.snd prK (pt ≫ prK)) hψw
  have hψt : ψ ≫ tN = tF := by
    simp only [ψ, tN, pullback.lift_snd_assoc, tF, σ]
    rw [← reassoc_of% hFKcond]
  have hψθG : ψ ≫ θG = π ≫ prG := by
    have hnat := L.mul_natural tN tF ψ hψt x1 x2
    have e1 : GoodReductionJacobian.schemeHomOverComp ψ hψt x1 = pK := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, x1, pK, ψ, pullback.lift_snd_assoc]
    have e2 : GoodReductionJacobian.schemeHomOverComp ψ hψt x2 = L.mul tF (L.inv tF pK) uu := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, x2, ψ, pullback.lift_fst_assoc]
      exact hn1
    have hval := congrArg Subtype.val hnat
    rw [e1, e2, mul_inv_mul_cancel L tF pK uu] at hval
    simpa only [GoodReductionJacobian.schemeHomOverComp_coe] using hval
  have hψθ : ψ ≫ θ = π := by
    apply pullback.hom_ext
    · simp only [θ, Category.assoc, pullback.lift_fst]
      exact hψθG
    · simp only [θ, Category.assoc, pullback.lift_snd]
      simp only [ψ, pullback.lift_snd_assoc]
      exact hFKcond.symm
  have hθ : Function.Surjective θ := by
    intro z
    obtain ⟨w, rfl⟩ := hπ z
    exact ⟨ψ w, by rw [← Scheme.Hom.comp_apply, hψθ]⟩
  exact hθ.connectedSpace θ.continuous

include hq hker in
theorem geometricallyConnected [GeometricallyConnected (i ≫ f)] [Surjective q.1] :
    GeometricallyConnected q.1 := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have : ConnectedSpace ↑(pullback q.1 y) := connectedSpace_pullback L i LQ q hq hker y
  exact (h.isoPullback.inv.surjective).connectedSpace h.isoPullback.inv.continuous

include hq hker in
theorem connectedSpace_preimage [GeometricallyConnected (i ≫ f)] [Surjective q.1]
    (h : ℕ) [SmoothOfRelativeDimension h q.1]
    {M : Scheme.{u}} (j : M ⟶ Q) [ConnectedSpace ↑M] :
    ConnectedSpace ↑(pullback j q.1) := by
  have : GeometricallyConnected q.1 := geometricallyConnected L i LQ q hq hker
  have : Smooth q.1 := SmoothOfRelativeDimension.smooth h q.1
  have : UniversallyOpen q.1 := inferInstance
  infer_instance

end main

end LiftConn

theorem solution
    (k : Type u) [Field k]
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
          NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x)
    [IsAffine N] [GeometricallyConnected (i ≫ f)]
    (h : ℕ) [SmoothOfRelativeDimension h q.1] [Surjective q.1] [QuasiCompact q.1]
    {M : Scheme.{u}} (j : M ⟶ Q) [IsClosedImmersion j] [ConnectedSpace M] :
    ConnectedSpace ↥(pullback q.1 j) := by
  have : GeometricallyConnected q.1 := LiftConn.geometricallyConnected L i LQ q hq hker
  have : Smooth q.1 := SmoothOfRelativeDimension.smooth h q.1
  have : UniversallyOpen q.1 := inferInstance
  infer_instance

end S_GoodReductionJacobian_RelativeGroupLaw_connectedSpace_pullback_of_comp_eq_one_iff
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_connectedSpace_pullback_of_comp_eq_one_iff (solution)
