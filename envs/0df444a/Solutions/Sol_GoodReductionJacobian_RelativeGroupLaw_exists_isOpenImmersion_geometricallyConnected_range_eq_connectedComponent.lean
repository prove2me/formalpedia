-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f01917d7-d94f-5e3f-8023-64f7474c89fe

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace

noncomputable section

universe u

namespace P2mIdCompField

section Maps

variable {k : Type u} [Field k] {N : Scheme.{u}} {gN : N ⟶ Spec (CommRingCat.of k)}
  (LN : RelativeGroupLaw k gN)

local notation "pt" => 𝟙 (Spec (CommRingCat.of k))

def const {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (s : SchemeHomOver pt gN) :
    SchemeHomOver t gN :=
  GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) s

@[scoped simp]
theorem const_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (s : SchemeHomOver pt gN) :
    (const t s).1 = t ≫ s.1 := rfl

theorem const_pt (s : SchemeHomOver pt gN) : const pt s = s :=
  Subtype.ext (Category.id_comp _)

theorem const_transition {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (s : SchemeHomOver pt gN) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (const t s) = const t' s :=
  Subtype.ext (by simp [← hψ])

theorem const_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (s s' : SchemeHomOver pt gN) :
    const t (LN.mul pt s s') = LN.mul t (const t s) (const t s') :=
  LN.mul_natural pt t t (Category.comp_id t) s s'

theorem const_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    const t (LN.one pt) = LN.one t :=
  LN.one_natural pt t t (Category.comp_id t)

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t gN) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (LN.inv t x) =
      LN.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := LN.pointGroup t'
  have h : GoodReductionJacobian.schemeHomOverComp ψ hψ (LN.inv t x) *
      GoodReductionJacobian.schemeHomOverComp ψ hψ x = 1 := by
    show LN.mul t' _ _ = LN.one t'
    rw [← LN.mul_natural t t' ψ hψ, LN.inv_mul_cancel, LN.one_natural]
  exact eq_inv_of_mul_eq_one_left h

def transl (s : SchemeHomOver pt gN) : N ⟶ N :=
  (LN.mul gN (const gN s) RelativeGroupLaw.idPoint).1

theorem comp_transl {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t gN)
    (s : SchemeHomOver pt gN) : x.1 ≫ transl LN s = (LN.mul t (const t s) x).1 := by
  have h := LN.mul_natural gN t x.1 x.2 (const gN s) RelativeGroupLaw.idPoint
  have h1 : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (const gN s) = const t s :=
    const_transition gN t x.1 x.2 s
  have h2 : GoodReductionJacobian.schemeHomOverComp x.1 x.2
      (RelativeGroupLaw.idPoint : SchemeHomOver gN gN) = x :=
    Subtype.ext (Category.comp_id _)
  rw [h1, h2] at h
  exact congrArg Subtype.val h

theorem transl_one : transl LN (LN.one pt) = 𝟙 N := by
  have h := comp_transl LN (RelativeGroupLaw.idPoint : SchemeHomOver gN gN) (LN.one pt)
  rw [const_one, LN.one_mul] at h
  simpa using h

theorem transl_comp (s s' : SchemeHomOver pt gN) :
    transl LN s ≫ transl LN s' = transl LN (LN.mul pt s' s) := by
  have h := comp_transl LN (LN.mul gN (const gN s) RelativeGroupLaw.idPoint) s'
  rw [← LN.mul_assoc, ← const_mul] at h
  exact h

scoped instance isIso_transl (s : SchemeHomOver pt gN) : IsIso (transl LN s) := by
  letI := LN.pointGroup pt
  refine ⟨⟨transl LN (LN.inv pt s), ?_, ?_⟩⟩
  · rw [transl_comp, show LN.mul pt (LN.inv pt s) s = LN.one pt from LN.inv_mul_cancel pt s,
      transl_one]
  · rw [transl_comp, show LN.mul pt s (LN.inv pt s) = LN.one pt from LN.mul_inv_cancel pt s,
      transl_one]

abbrev clpt (x : SchemeHomOver pt gN) : N := x.1 (IsLocalRing.closedPoint k)

theorem transl_clpt (x s : SchemeHomOver pt gN) :
    transl LN s (clpt x) = clpt (LN.mul pt s x) := by
  have h := comp_transl LN x s
  rw [const_pt] at h
  show (x.1 ≫ transl LN s) (IsLocalRing.closedPoint k) = _
  rw [h]

theorem range_coe_eq (x : SchemeHomOver pt gN) : Set.range x.1 = {clpt x} := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    have : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [this]; rfl
  · rintro rfl; exact ⟨_, rfl⟩

def invN : N ⟶ N := (LN.inv gN RelativeGroupLaw.idPoint).1

theorem comp_invN {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t gN) :
    x.1 ≫ invN LN = (LN.inv t x).1 := by
  have h := inv_natural LN gN t x.1 x.2 RelativeGroupLaw.idPoint
  have h2 : GoodReductionJacobian.schemeHomOverComp x.1 x.2
      (RelativeGroupLaw.idPoint : SchemeHomOver gN gN) = x :=
    Subtype.ext (Category.comp_id _)
  rw [h2] at h
  exact congrArg Subtype.val h

theorem invN_invN : invN LN ≫ invN LN = 𝟙 N := by
  letI := LN.pointGroup gN
  have h := comp_invN LN (LN.inv gN RelativeGroupLaw.idPoint)
  rw [show LN.inv gN (LN.inv gN RelativeGroupLaw.idPoint) = RelativeGroupLaw.idPoint from
    inv_inv (RelativeGroupLaw.idPoint : SchemeHomOver gN gN)] at h
  exact h

scoped instance isIso_invN : IsIso (invN LN) := ⟨⟨invN LN, invN_invN LN, invN_invN LN⟩⟩

theorem invN_clpt (x : SchemeHomOver pt gN) : invN LN (clpt x) = clpt (LN.inv pt x) := by
  show (x.1 ≫ invN LN) (IsLocalRing.closedPoint k) = _
  rw [comp_invN]

abbrev ePt : N := clpt (LN.one pt)

theorem invN_ePt : invN LN (ePt LN) = ePt LN := by
  letI := LN.pointGroup pt
  rw [invN_clpt, show LN.inv pt (LN.one pt) = LN.one pt from inv_one]

theorem transl_ePt (s : SchemeHomOver pt gN) : transl LN s (ePt LN) = clpt s := by
  rw [transl_clpt, LN.mul_one]

end Maps

section Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

theorem homeomorph_image_connectedComponent (h : α ≃ₜ β) (x : α) :
    h '' connectedComponent x = connectedComponent (h x) := by
  refine Set.Subset.antisymm (h.continuous.image_connectedComponent_subset _) ?_
  intro y hy
  have h1 : h.symm '' connectedComponent (h x) ⊆ connectedComponent (h.symm (h x)) :=
    h.symm.continuous.image_connectedComponent_subset (h x)
  rw [h.symm_apply_apply] at h1
  exact ⟨h.symm y, h1 ⟨y, hy, rfl⟩, h.apply_symm_apply y⟩

theorem eq_connectedComponent_of_isClopen_of_isPreconnected {s : Set α} (hs : IsClopen s)
    (hc : IsPreconnected s) {x : α} (hx : x ∈ s) : s = connectedComponent x :=
  Set.Subset.antisymm (hc.subset_connectedComponent hx) (hs.connectedComponent_subset hx)

theorem isOpen_connectedComponent_of_finite_irreducibleComponents
    (hfin : (irreducibleComponents α).Finite) (x : α) : IsOpen (connectedComponent x) := by
  have hcompl : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents α | Disjoint Z (connectedComponent x)}, Z := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩,
        mem_irreducibleComponent⟩
      rw [Set.disjoint_left]
      intro z hz hzx
      have h1 : irreducibleComponent y ⊆ connectedComponent z :=
        (isIrreducible_irreducibleComponent).isConnected.isPreconnected.subset_connectedComponent hz
      have h2 : connectedComponent x = connectedComponent z := connectedComponent_eq hzx
      exact hy (h2 ▸ h1 mem_irreducibleComponent)
    · rintro ⟨Z, ⟨-, hdis⟩, hyZ⟩ hy
      exact Set.disjoint_left.mp hdis hyZ hy
  rw [← isClosed_compl_iff, hcompl]
  exact Set.Finite.isClosed_biUnion (hfin.subset fun Z hZ => hZ.1)
    fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1

end Topology

section IdComp

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f)

local notation "pt" => 𝟙 (Spec (CommRingCat.of k))

def idC : Set G := connectedComponent (ePt L)

theorem ePt_mem_idC : ePt L ∈ idC L := mem_connectedComponent

include L in

private theorem _root_.P2mIdCompField.finite_irreducibleComponents : (irreducibleComponents G).Finite := by
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : IsNoetherian G := ⟨⟩
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

p2m_export "P2mIdCompField" "finite_irreducibleComponents"

theorem isOpen_idC : IsOpen (idC L) :=
  isOpen_connectedComponent_of_finite_irreducibleComponents (finite_irreducibleComponents L) _

theorem isClosed_idC : IsClosed (idC L) := isClosed_connectedComponent

theorem isClopen_idC : IsClopen (idC L) := ⟨isClosed_idC L, isOpen_idC L⟩

theorem isConnected_idC : _root_.IsConnected (idC L) := isConnected_connectedComponent

def U₀ : G.Opens := ⟨idC L, isOpen_idC L⟩

abbrev G₀ : Scheme.{u} := (U₀ L : Scheme.{u})

abbrev ι₀ : G₀ L ⟶ G := (U₀ L).ι

abbrev f₀ : G₀ L ⟶ Spec (CommRingCat.of k) := ι₀ L ≫ f

theorem range_ι₀ : Set.range (ι₀ L) = idC L := (U₀ L).range_ι

theorem ι₀_apply_mem (a : G₀ L) : ι₀ L a ∈ idC L := by
  rw [← range_ι₀ L]; exact ⟨a, rfl⟩

scoped instance isClosedImmersion_ι₀ : IsClosedImmersion (ι₀ L) :=
  .of_isPreimmersion _ (by rw [range_ι₀]; exact isClosed_idC L)

scoped instance connectedSpace_G₀ : ConnectedSpace (G₀ L) := by
  have h : _root_.IsConnected (Set.range (ι₀ L)) := by rw [range_ι₀]; exact isConnected_idC L
  have e : Set.range (ι₀ L) ≃ₜ G₀ L := ((ι₀ L).isEmbedding.toHomeomorph).symm
  haveI := Subtype.connectedSpace h
  exact e.connectedSpace_iff.mp inferInstance

def liftPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (y : SchemeHomOver t f)
    (hy : Set.range y.1 ⊆ idC L) : SchemeHomOver t (f₀ L) :=
  ⟨IsOpenImmersion.lift (ι₀ L) y.1 (by rw [range_ι₀]; exact hy), by
    rw [IsOpenImmersion.lift_fac_assoc]; exact y.2⟩

@[scoped simp]
theorem liftPt_coe_ι₀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (y : SchemeHomOver t f)
    (hy : Set.range y.1 ⊆ idC L) : (liftPt L y hy).1 ≫ ι₀ L = y.1 :=
  IsOpenImmersion.lift_fac _ _ _

def e₀ : SchemeHomOver pt (f₀ L) :=
  liftPt L (L.one pt) (by
    rw [range_coe_eq]; exact Set.singleton_subset_iff.mpr (ePt_mem_idC L))

end IdComp

section BaseChange

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  (L : RelativeGroupLaw k f)
  {K : Type u} [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))

local notation "pt" => 𝟙 (Spec (CommRingCat.of k))
local notation "ptK" => 𝟙 (Spec (CommRingCat.of K))

theorem one_comp_eq (L : RelativeGroupLaw k f) {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) :
    (L.one s).1 = s ≫ (L.one pt).1 := by
  rw [← const_one L s, const_coe]

theorem fst_ePt_baseChange :
    pullback.fst f t (ePt (L.baseChange t)) = ePt L := by
  have h1 : ((L.baseChange t).one ptK).1 ≫ pullback.fst f t = (L.one (ptK ≫ t)).1 := by
    have h := congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_one t L ptK)
    rw [RelativeGroupLaw.baseChangePointToBase_coe] at h
    exact h
  have h2 : (L.one (ptK ≫ t)).1 = (ptK ≫ t) ≫ (L.one pt).1 := one_comp_eq L _
  show (((L.baseChange t).one ptK).1 ≫ pullback.fst f t) (IsLocalRing.closedPoint K) = _
  rw [h1, h2, Category.id_comp, Scheme.Hom.comp_apply]
  show (L.one pt).1 (t (IsLocalRing.closedPoint K)) = (L.one pt).1 (IsLocalRing.closedPoint k)
  congr 1
  exact Subsingleton.elim _ _

theorem subsingleton_pullback_one_fst :
    Subsingleton ↥(pullback (L.one pt).1 (pullback.fst f t)) := by
  let e1 : pullback (L.one pt).1 (pullback.fst f t) ≅ pullback ((L.one pt).1 ≫ f) t :=
    pullbackRightPullbackFstIso f t (L.one pt).1
  let e2 : pullback ((L.one pt).1 ≫ f) t ≅ pullback (𝟙 (Spec (CommRingCat.of k))) t :=
    pullback.congrHom (L.one pt).2 rfl
  haveI : IsIso (pullback.snd (𝟙 (Spec (CommRingCat.of k))) t) := inferInstance
  let e3 : ↥(pullback (𝟙 (Spec (CommRingCat.of k))) t) ≃ₜ ↥(Spec (CommRingCat.of K)) :=
    (pullback.snd (𝟙 (Spec (CommRingCat.of k))) t).homeomorph
  have e : ↥(pullback (L.one pt).1 (pullback.fst f t)) ≃ₜ ↥(Spec (CommRingCat.of K)) :=
    (e1 ≪≫ e2).hom.homeomorph.trans e3
  exact e.toEquiv.subsingleton

theorem eq_ePt_of_fst_eq {z : ↥(pullback f t)} (hz : pullback.fst f t z = ePt L) :
    z = ePt (L.baseChange t) := by
  have hr : Set.range (pullback.snd (L.one pt).1 (pullback.fst f t)) =
      pullback.fst f t ⁻¹' {ePt L} := by
    rw [Scheme.Pullback.range_snd, range_coe_eq]
  have hz' : z ∈ Set.range (pullback.snd (L.one pt).1 (pullback.fst f t)) := by
    rw [hr]; exact hz
  have he' : ePt (L.baseChange t) ∈ Set.range (pullback.snd (L.one pt).1 (pullback.fst f t)) := by
    rw [hr]; exact fst_ePt_baseChange L t
  obtain ⟨a, rfl⟩ := hz'
  obtain ⟨b, hb⟩ := he'
  haveI := subsingleton_pullback_one_fst L t
  rw [← hb, Subsingleton.elim a b]

theorem isClopen_preimage_idC [LocallyOfFiniteType f] [QuasiCompact f] :
    IsClopen (pullback.fst f t ⁻¹' idC L) :=
  (isClopen_idC L).preimage (pullback.fst f t).continuous

theorem ePt_baseChange_mem_preimage [LocallyOfFiniteType f] [QuasiCompact f] :
    ePt (L.baseChange t) ∈ pullback.fst f t ⁻¹' idC L := by
  show pullback.fst f t (ePt (L.baseChange t)) ∈ idC L
  rw [fst_ePt_baseChange]
  exact ePt_mem_idC L

end BaseChange

section AlgClosure

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f)
  {K : Type u} [Field K] [IsAlgClosed K] [Algebra k K] [Algebra.IsIntegral k K]

local notation "pt" => 𝟙 (Spec (CommRingCat.of k))
local notation "ptK" => 𝟙 (Spec (CommRingCat.of K))

variable (k K) in

def tb : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

scoped instance isIntegralHom_tb : IsIntegralHom (tb k K) := by
  rw [tb, IsIntegralHom.SpecMap_iff]
  intro x
  exact Algebra.IsIntegral.isIntegral (R := k) x

scoped instance surjective_tb : Surjective (tb k K) :=
  ⟨fun _ => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩

theorem exists_mem_image_connectedComponent (y : ↥(pullback f (tb k K))) :
    ∃ s : SchemeHomOver ptK (pullback.snd f (tb k K)),
      y ∈ (transl (L.baseChange (tb k K)) s).homeomorph '' idC (L.baseChange (tb k K)) := by
  set L' := L.baseChange (tb k K)
  haveI : JacobsonSpace ↥(pullback f (tb k K)) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd f (tb k K))
  obtain ⟨z, hzZ, hz⟩ := nonempty_inter_closedPoints (connectedComponent_nonempty (x := y))
    isClosed_connectedComponent.isLocallyClosed
  let s : SchemeHomOver ptK (pullback.snd f (tb k K)) :=
    (pointEquivClosedPoint (pullback.snd f (tb k K))).symm ⟨z, hz⟩
  have hs : clpt s = z := by
    have h := congrArg Subtype.val
      ((pointEquivClosedPoint (pullback.snd f (tb k K))).apply_symm_apply ⟨z, hz⟩)
    simpa only [pointEquivClosedPoint_apply_coe] using h
  refine ⟨s, ?_⟩
  rw [idC, homeomorph_image_connectedComponent]
  show y ∈ connectedComponent (transl L' s (ePt L'))
  rw [transl_ePt, hs, ← connectedComponent_eq hzZ]
  exact mem_connectedComponent

theorem preimage_idC_eq_idC :
    pullback.fst f (tb k K) ⁻¹' idC L = idC (L.baseChange (tb k K)) := by
  set p := pullback.fst f (tb k K)
  set L' := L.baseChange (tb k K)
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    obtain ⟨s, hys⟩ := exists_mem_image_connectedComponent L y
    set h := (transl L' s).homeomorph
    set E := h '' idC L'
    have hEclopen : IsClopen E :=
      ⟨h.isClosed_image.mpr (isClopen_idC L').1, h.isOpen_image.mpr (isClopen_idC L').2⟩
    have hEconn : _root_.IsPreconnected E :=
      (isConnected_idC L').isPreconnected.image _ h.continuous.continuousOn

    have hpE_open : IsOpen (p '' E) := p.isOpenMap _ hEclopen.2
    have hpE_closed : IsClosed (p '' E) := p.isClosedMap _ hEclopen.1
    have hpE_conn : _root_.IsPreconnected (p '' E) := hEconn.image _ p.continuous.continuousOn
    have hpE_eq : p '' E = connectedComponent (p y) :=
      eq_connectedComponent_of_isClopen_of_isPreconnected ⟨hpE_closed, hpE_open⟩ hpE_conn
        ⟨y, hys, rfl⟩
    have hidC : idC L = connectedComponent (p y) := connectedComponent_eq hy
    have he : ePt L ∈ p '' E := by rw [hpE_eq, ← hidC]; exact ePt_mem_idC L
    obtain ⟨z, hzE, hz⟩ := he
    have hz' : z = ePt L' := eq_ePt_of_fst_eq L (tb k K) hz

    have h1 : E = connectedComponent (h (ePt L')) := homeomorph_image_connectedComponent h _
    have hmem : ePt L' ∈ connectedComponent (h (ePt L')) := by rw [← h1, ← hz']; exact hzE
    have hE : E = idC L' := by rw [h1, idC]; exact connectedComponent_eq hmem
    rw [← hE]; exact hys
  · rw [idC, idC, ← fst_ePt_baseChange L (tb k K)]
    exact Set.image_subset_iff.mp (p.continuous.image_connectedComponent_subset _)

end AlgClosure

section Geometric

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f)

local notation "pt" => 𝟙 (Spec (CommRingCat.of k))

theorem isIrreducible_idC_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K] {G' : Scheme.{u}}
    {f' : G' ⟶ Spec (CommRingCat.of K)} [LocallyOfFiniteType f'] [QuasiCompact f']
    (L' : RelativeGroupLaw K f') : IsIrreducible (idC L') := by
  obtain ⟨G₀', i, -, -, -, hirr, hrange, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
      K L'
  haveI := hirr
  have h : idC L' = Set.range i := by rw [hrange]; rfl
  rw [h, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ i.continuous.continuousOn

theorem irreducibleSpace_G₀_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K]
    {G' : Scheme.{u}} {f' : G' ⟶ Spec (CommRingCat.of K)} [LocallyOfFiniteType f']
    [QuasiCompact f'] (L' : RelativeGroupLaw K f') : IrreducibleSpace (G₀ L') := by
  have h : IsIrreducible (Set.range (ι₀ L')) := by
    rw [range_ι₀]; exact isIrreducible_idC_of_isAlgClosed L'
  have e : Set.range (ι₀ L') ≃ₜ G₀ L' := ((ι₀ L').isEmbedding.toHomeomorph).symm
  haveI := Subtype.irreducibleSpace h
  exact e.irreducibleSpace_iff.mp inferInstance

theorem geometricallyIrreducible_f₀_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K]
    {G' : Scheme.{u}} {f' : G' ⟶ Spec (CommRingCat.of K)} [LocallyOfFiniteType f']
    [QuasiCompact f'] (L' : RelativeGroupLaw K f') : GeometricallyIrreducible (f₀ L') := by
  haveI := irreducibleSpace_G₀_of_isAlgClosed L'
  exact AlgebraicGeometry.GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed (f₀ L')

theorem geometricallyIrreducible_of_snd {X : Scheme.{u}} (h : X ⟶ Spec (CommRingCat.of k))
    {K : Type u} [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [Surjective t]
    [hgi : GeometricallyIrreducible (pullback.snd h t)] : GeometricallyIrreducible h := by
  refine ⟨(geometrically_iff_of_isClosedUnderIsomorphisms (P := (IrreducibleSpace ·))).mpr
    fun K' _ y => ?_⟩
  let W : Scheme.{u} := pullback y t
  haveI : Nonempty ↥W := by
    obtain ⟨w, -⟩ := (pullback.fst y t).surjective (IsLocalRing.closedPoint K')
    exact ⟨w⟩
  let w : ↥W := Classical.arbitrary _
  let m : Spec (W.residueField w) ⟶ W := W.fromSpecResidueField w

  have h1 : IrreducibleSpace ↥(pullback (pullback.snd h t) (m ≫ pullback.snd y t)) :=
    pullback_of_geometrically hgi.1 _ _
  have h2 : IrreducibleSpace ↥(pullback h ((m ≫ pullback.snd y t) ≫ t)) :=
    (pullbackLeftPullbackSndIso h t (m ≫ pullback.snd y t)).hom.homeomorph.irreducibleSpace_iff.mp
      h1
  have heq : (m ≫ pullback.snd y t) ≫ t = (m ≫ pullback.fst y t) ≫ y := by
    simp only [Category.assoc, pullback.condition]
  have h3 : IrreducibleSpace ↥(pullback h ((m ≫ pullback.fst y t) ≫ y)) :=
    (pullback.congrHom (rfl : h = h) heq).hom.homeomorph.irreducibleSpace_iff.mp h2
  have h4 : IrreducibleSpace ↥(pullback (pullback.snd h y) (m ≫ pullback.fst y t)) :=
    (pullbackLeftPullbackSndIso h y (m ≫ pullback.fst y t)).hom.homeomorph.irreducibleSpace_iff.mpr
      h3

  haveI : Surjective (m ≫ pullback.fst y t) :=
    ⟨fun _ => ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
  have hs : Function.Surjective (pullback.fst (pullback.snd h y) (m ≫ pullback.fst y t)) :=
    (pullback.fst (pullback.snd h y) (m ≫ pullback.fst y t)).surjective
  have h5 : IsIrreducible (Set.univ : Set ↥(pullback h y)) := by
    rw [← hs.range_eq, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (Scheme.Hom.continuous _).continuousOn
  exact (irreducibleSpace_def _).mpr h5

variable {K : Type u} [Field K] [IsAlgClosed K] [Algebra k K] [Algebra.IsIntegral k K]

theorem range_snd_ι₀_fst :
    Set.range (pullback.snd (ι₀ L) (pullback.fst f (tb k K))) = idC (L.baseChange (tb k K)) := by
  rw [Scheme.Pullback.range_snd, range_ι₀, preimage_idC_eq_idC]

def isoG₀b : pullback (ι₀ L) (pullback.fst f (tb k K)) ≅ G₀ (L.baseChange (tb k K)) :=
  IsOpenImmersion.isoOfRangeEq (pullback.snd (ι₀ L) (pullback.fst f (tb k K)))
    (ι₀ (L.baseChange (tb k K))) (by rw [range_snd_ι₀_fst, range_ι₀])

@[reassoc]
theorem isoG₀b_hom_ι₀ :
    (isoG₀b L (K := K)).hom ≫ ι₀ (L.baseChange (tb k K)) =
      pullback.snd (ι₀ L) (pullback.fst f (tb k K)) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem snd_f₀_tb_eq :
    pullback.snd (f₀ L) (tb k K) =
      (pullbackRightPullbackFstIso f (tb k K) (ι₀ L)).inv ≫ (isoG₀b L (K := K)).hom ≫
        f₀ (L.baseChange (tb k K)) := by
  rw [Iso.eq_inv_comp, pullbackRightPullbackFstIso_hom_snd, isoG₀b_hom_ι₀_assoc]

theorem geometricallyIrreducible_snd_f₀_tb :
    GeometricallyIrreducible (pullback.snd (f₀ L) (tb k K)) := by
  rw [snd_f₀_tb_eq,
    MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIrreducible),
    MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIrreducible)]
  exact geometricallyIrreducible_f₀_of_isAlgClosed _

scoped instance geometricallyIrreducible_f₀ : GeometricallyIrreducible (f₀ L) :=
  haveI := geometricallyIrreducible_snd_f₀_tb L (K := AlgebraicClosure k)
  geometricallyIrreducible_of_snd (f₀ L) (tb k (AlgebraicClosure k))

scoped instance geometricallyConnected_f₀ : GeometricallyConnected (f₀ L) :=
  AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected (f₀ L)

scoped instance irreducibleSpace_G₀ : IrreducibleSpace (G₀ L) :=
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f₀ L)

end Geometric

section Compat

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f)

theorem preimage_range_ι₀_eq {K : Type u} [Field K]
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :
    pullback.fst f t ⁻¹' Set.range (ι₀ L) = connectedComponent (ePt (L.baseChange t)) := by
  have hconn : _root_.IsPreconnected (pullback.fst f t ⁻¹' Set.range (ι₀ L)) := by
    rw [← Scheme.Pullback.range_snd]
    haveI : ConnectedSpace ↥(pullback (ι₀ L) (pullback.fst f t)) :=
      (pullbackRightPullbackFstIso f t (ι₀ L)).hom.homeomorph.connectedSpace_iff.mpr inferInstance
    exact isPreconnected_range (pullback.snd (ι₀ L) (pullback.fst f t)).continuous
  refine eq_connectedComponent_of_isClopen_of_isPreconnected ?_ hconn ?_
  · rw [range_ι₀]; exact isClopen_preimage_idC L t
  · rw [range_ι₀]; exact ePt_baseChange_mem_preimage L t

end Compat

section Law

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f)

local notation "pt" => 𝟙 (Spec (CommRingCat.of k))

def toG {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t (f₀ L)) :
    SchemeHomOver t f :=
  ⟨x.1 ≫ ι₀ L, by rw [Category.assoc]; exact x.2⟩

@[scoped simp]
theorem toG_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t (f₀ L)) :
    (toG L x).1 = x.1 ≫ ι₀ L := rfl

theorem toG_injective {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} :
    Function.Injective (toG L (T := T) (t := t)) := by
  intro x y h
  exact Subtype.ext ((cancel_mono (ι₀ L)).mp (congrArg Subtype.val h))

theorem toG_transition {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t (f₀ L)) :
    toG L (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (toG L x) :=
  Subtype.ext (Category.assoc _ _ _)

@[scoped simp]
theorem toG_liftPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (y : SchemeHomOver t f)
    (hy : Set.range y.1 ⊆ idC L) : toG L (liftPt L y hy) = y :=
  Subtype.ext (liftPt_coe_ι₀ _ _ _)

def M : pullback (f₀ L) (f₀ L) ⟶ G :=
  (L.mul (pullback.fst (f₀ L) (f₀ L) ≫ f₀ L)
    ⟨pullback.fst _ _ ≫ ι₀ L, by simp⟩
    ⟨pullback.snd _ _ ≫ ι₀ L, by simpa using pullback.condition.symm⟩).1

theorem lift_M {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (a b : T ⟶ G₀ L) (ha : a ≫ f₀ L = t) (hb : b ≫ f₀ L = t) :
    pullback.lift a b (ha.trans hb.symm) ≫ M L =
      (L.mul t ⟨a ≫ ι₀ L, by simpa using ha⟩ ⟨b ≫ ι₀ L, by simpa using hb⟩).1 := by
  have hψ : pullback.lift a b (ha.trans hb.symm) ≫ (pullback.fst (f₀ L) (f₀ L) ≫ f₀ L) = t := by
    rw [pullback.lift_fst_assoc, ha]
  have hnat := L.mul_natural _ t (pullback.lift a b (ha.trans hb.symm)) hψ
    ⟨pullback.fst _ _ ≫ ι₀ L, by simp⟩
    ⟨pullback.snd _ _ ≫ ι₀ L, by simpa using pullback.condition.symm⟩
  have h1 : GoodReductionJacobian.schemeHomOverComp (pullback.lift a b (ha.trans hb.symm)) hψ
      (⟨pullback.fst _ _ ≫ ι₀ L, by simp⟩ : SchemeHomOver _ f) =
      ⟨a ≫ ι₀ L, by simpa using ha⟩ :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc,
      pullback.lift_fst])
  have h2 : GoodReductionJacobian.schemeHomOverComp (pullback.lift a b (ha.trans hb.symm)) hψ
      (⟨pullback.snd _ _ ≫ ι₀ L, by simpa using pullback.condition.symm⟩ : SchemeHomOver _ f) =
      ⟨b ≫ ι₀ L, by simpa using hb⟩ :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc,
      pullback.lift_snd])
  rw [h1, h2] at hnat
  exact congrArg Subtype.val hnat

theorem range_M_subset : Set.range (M L) ⊆ idC L := by
  have hconn : _root_.IsPreconnected (Set.range (M L)) := isPreconnected_range (M L).continuous
  have he : ePt L ∈ Set.range (M L) := by
    have hj := lift_M L pt (e₀ L).1 (e₀ L).1 (e₀ L).2 (e₀ L).2
    have h1 : (⟨(e₀ L).1 ≫ ι₀ L, by simpa using (e₀ L).2⟩ : SchemeHomOver pt f) = L.one pt :=
      Subtype.ext (liftPt_coe_ι₀ _ _ _)
    rw [h1, L.mul_one] at hj
    exact ⟨pullback.lift (e₀ L).1 (e₀ L).1 (((e₀ L).2).trans ((e₀ L).2).symm)
      (IsLocalRing.closedPoint k), by rw [← Scheme.Hom.comp_apply, hj]⟩
  exact hconn.subset_connectedComponent he

theorem range_mul_toG_subset {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t (f₀ L)) :
    Set.range (L.mul t (toG L x) (toG L y)).1 ⊆ idC L := by
  have h : (L.mul t (toG L x) (toG L y)).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ M L := by
    rw [lift_M L t x.1 y.1 x.2 y.2]; rfl
  rw [h, Scheme.Hom.comp_base, TopCat.coe_comp]
  exact (Set.range_comp_subset_range _ _).trans (range_M_subset L)

theorem range_one_subset {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    Set.range (L.one t).1 ⊆ idC L := by
  rw [← const_one L t, const_coe, Scheme.Hom.comp_base, TopCat.coe_comp]
  refine (Set.range_comp_subset_range _ _).trans ?_
  rw [range_coe_eq]
  exact Set.singleton_subset_iff.mpr (ePt_mem_idC L)

theorem range_ι₀_invN_subset : Set.range (ι₀ L ≫ invN L) ⊆ idC L := by
  let h : G ≃ₜ G := (invN L).homeomorph
  have h1 : h '' idC L = idC L := by
    rw [idC, homeomorph_image_connectedComponent]
    show connectedComponent (invN L (ePt L)) = _
    rw [invN_ePt]
  rintro _ ⟨a, rfl⟩
  rw [← h1]
  exact ⟨ι₀ L a, ι₀_apply_mem L a, rfl⟩

theorem range_inv_toG_subset {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x : SchemeHomOver t (f₀ L)) :
    Set.range (L.inv t (toG L x)).1 ⊆ idC L := by
  rw [← comp_invN L (toG L x), toG_coe, Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp]
  exact (Set.range_comp_subset_range _ _).trans (range_ι₀_invN_subset L)

def mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (f₀ L)) :
    SchemeHomOver t (f₀ L) :=
  liftPt L (L.mul t (toG L x) (toG L y)) (range_mul_toG_subset L t x y)

theorem toG_mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t (f₀ L)) :
    toG L (mulPt L t x y) = L.mul t (toG L x) (toG L y) :=
  toG_liftPt _ _ _

def onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) : SchemeHomOver t (f₀ L) :=
  liftPt L (L.one t) (range_one_subset L t)

theorem toG_onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    toG L (onePt L t) = L.one t :=
  toG_liftPt _ _ _

def invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (f₀ L)) :
    SchemeHomOver t (f₀ L) :=
  liftPt L (L.inv t (toG L x)) (range_inv_toG_subset L t x)

theorem toG_invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x : SchemeHomOver t (f₀ L)) : toG L (invPt L t x) = L.inv t (toG L x) :=
  toG_liftPt _ _ _

def law₀ : RelativeGroupLaw k (f₀ L) where
  mul t x y := mulPt L t x y
  one t := onePt L t
  inv t x := invPt L t x
  mul_assoc t x y z := by
    apply toG_injective L
    simp only [toG_mulPt]
    exact L.mul_assoc t _ _ _
  one_mul t x := by
    apply toG_injective L
    simp only [toG_mulPt, toG_onePt]
    exact L.one_mul t _
  mul_one t x := by
    apply toG_injective L
    simp only [toG_mulPt, toG_onePt]
    exact L.mul_one t _
  inv_mul_cancel t x := by
    apply toG_injective L
    simp only [toG_mulPt, toG_invPt, toG_onePt]
    exact L.inv_mul_cancel t _
  mul_natural t t' ψ hψ x y := by
    apply toG_injective L
    rw [toG_transition]
    simp only [toG_mulPt]
    rw [L.mul_natural t t' ψ hψ, toG_transition, toG_transition]

theorem toG_law₀_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t (f₀ L)) :
    toG L ((law₀ L).mul t x y) = L.mul t (toG L x) (toG L y) :=
  toG_mulPt L t x y

theorem hom_ι₀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (f₀ L)) :
    NeronModelInfra.schemeHomOverComp ((law₀ L).mul t x y) (⟨ι₀ L, rfl⟩ : SchemeHomOver (f₀ L) f) =
      L.mul t (NeronModelInfra.schemeHomOverComp x (⟨ι₀ L, rfl⟩ : SchemeHomOver (f₀ L) f))
        (NeronModelInfra.schemeHomOverComp y (⟨ι₀ L, rfl⟩ : SchemeHomOver (f₀ L) f)) :=
  toG_law₀_mul L t x y

theorem isCommutative_law₀ (hc : L.IsCommutative) : (law₀ L).IsCommutative := by
  intro T t x y
  apply toG_injective L
  rw [toG_law₀_mul, toG_law₀_mul]
  exact hc t _ _

end Law

section FiniteIndex

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f)

local notation "pt" => 𝟙 (Spec (CommRingCat.of k))

theorem clpt_mul_inv_mem_idC (x s : SchemeHomOver pt f) (hs : clpt s ∈ connectedComponent (clpt x)) :
    clpt (L.mul pt (L.inv pt s) x) ∈ idC L := by
  letI := L.pointGroup pt
  let φ : G ≃ₜ G := (transl L (L.inv pt s)).homeomorph
  have h1 : φ (clpt s) = ePt L := by
    show transl L (L.inv pt s) (clpt s) = _
    rw [transl_clpt, show L.mul pt (L.inv pt s) s = L.one pt from inv_mul_cancel s]
  have h2 : φ (clpt x) = clpt (L.mul pt (L.inv pt s) x) := by
    show transl L (L.inv pt s) (clpt x) = _
    rw [transl_clpt]
  have h3 : φ '' connectedComponent (clpt s) = idC L := by
    rw [homeomorph_image_connectedComponent, h1]; rfl
  rw [← h2, ← h3]
  refine ⟨clpt x, ?_, rfl⟩
  rw [← connectedComponent_eq hs]
  exact mem_connectedComponent

theorem exists_finite_cosets :
    ∃ S : Set (SchemeHomOver pt f), S.Finite ∧
      ∀ x : SchemeHomOver pt f, ∃ s ∈ S, ∃ a : SchemeHomOver pt (f₀ L),
        x = L.mul pt s (NeronModelInfra.schemeHomOverComp a (⟨ι₀ L, rfl⟩ : SchemeHomOver (f₀ L) f)) := by
  classical
  letI := L.pointGroup pt
  haveI : Finite (irreducibleComponents G) := (finite_irreducibleComponents L).to_subtype

  let I := {Z : irreducibleComponents G // ∃ s : SchemeHomOver pt f, clpt s ∈ (Z : Set G)}
  choose rep hrep using fun Z : I => Z.2
  refine ⟨Set.range rep, Set.finite_range rep, fun x => ?_⟩
  let Z : irreducibleComponents G :=
    ⟨irreducibleComponent (clpt x), irreducibleComponent_mem_irreducibleComponents _⟩
  let ZI : I := ⟨Z, x, mem_irreducibleComponent⟩
  let s := rep ZI
  have hsZ : clpt s ∈ irreducibleComponent (clpt x) := hrep ZI
  have hs : clpt s ∈ connectedComponent (clpt x) :=
    irreducibleComponent_subset_connectedComponent hsZ
  have hy := clpt_mul_inv_mem_idC L x s hs
  let a : SchemeHomOver pt (f₀ L) :=
    liftPt L (L.mul pt (L.inv pt s) x) (by
      rw [range_coe_eq]; exact Set.singleton_subset_iff.mpr hy)
  refine ⟨s, ⟨ZI, rfl⟩, a, ?_⟩
  have ha : NeronModelInfra.schemeHomOverComp a (⟨ι₀ L, rfl⟩ : SchemeHomOver (f₀ L) f) =
      L.mul pt (L.inv pt s) x :=
    Subtype.ext (liftPt_coe_ι₀ _ _ _)
  rw [ha]
  show x = s * (s⁻¹ * x)
  rw [mul_inv_cancel_left]

end FiniteIndex

end P2mIdCompField
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent.P2mIdCompField"

open P2mIdCompField in
theorem solution
    (k : Type u) [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f) :
    ∃ (G₀ : Scheme.{u}) (i : G₀ ⟶ G) (L₀ : RelativeGroupLaw k (i ≫ f)),
      IsOpenImmersion i ∧ IsClosedImmersion i ∧ IrreducibleSpace G₀ ∧
      GeometricallyIrreducible (i ≫ f) ∧ GeometricallyConnected (i ≫ f) ∧
      Set.range i =
        connectedComponent ((L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k)) ∧
      (∀ (K : Type u) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)),
        pullback.fst f t ⁻¹' Set.range i =
          connectedComponent
            (((L.baseChange t).one (𝟙 (Spec (CommRingCat.of K)))).1 (IsLocalRing.closedPoint K))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (L₀.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) ∧
      (L.IsCommutative → L₀.IsCommutative) ∧
      ∃ S : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f), S.Finite ∧
        ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
          ∃ s ∈ S, ∃ a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f),
            x = L.mul (𝟙 (Spec (CommRingCat.of k))) s
              (NeronModelInfra.schemeHomOverComp a (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)) := by
  obtain ⟨S, hS, hcos⟩ := exists_finite_cosets L
  exact ⟨G₀ L, ι₀ L, law₀ L, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, range_ι₀ L, fun K _ t => preimage_range_ι₀_eq L t, fun t x y => hom_ι₀ L t x y,
    isCommutative_law₀ L, S, hS, hcos⟩

end
end S_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent (solution)
