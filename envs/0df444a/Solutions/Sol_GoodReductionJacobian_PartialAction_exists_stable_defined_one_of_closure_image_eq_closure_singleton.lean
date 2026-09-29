-- Prove2me | solution 1 for GoodReductionJacobian.PartialAction.exists_stable_defined_one_of_closure_image_eq_closure_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/3cbb9726-684f-55ee-a6b7-5e6434e5480f

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction
import Theorems.Thm_AlgebraicGeometry_ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral
import Theorems.Thm_AlgebraicGeometry_exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
import Theorems.Thm_AlgebraicGeometry_jacobsonSpace_of_locallyOfFiniteType
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_PartialAction_exists_stable_defined_one_of_closure_image_eq_closure_singleton
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_PartialAction_exists_stable_defined_one_of_closure_image_eq_closure_singleton.GoodReductionJacobian"
open Topology

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw PartialAction RelativeGroupLaw.exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex"
namespace PartialAction
p2m_export "GoodReductionJacobian.PartialAction" "pair Defined liftDom liftDom_ι act act_coe UnitActs Assoc Stable hom_comp dom hom"
namespace SweptDivisorB1e
p2m_open "GoodReductionJacobian.PartialAction GoodReductionJacobian"

section General

variable {k : Type u} [Field k]

theorem dim_closure_add_one_le {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsIntegral P] [LocallyOfFiniteType p] (w' : P)
    (hw'₁ : ringKrullDim (P.presheaf.stalk w') = 1) :
    topologicalKrullDim ↥(closure ({w'} : Set P)) + 1 ≤ topologicalKrullDim P := by
  have h := AlgebraicGeometry.ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral p w'
  rw [hw'₁, add_comm] at h
  exact h.le

theorem irreducibleSpace_of_connected [IsAlgClosed k] {G : Scheme.{u}}
    {f : G ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) : IrreducibleSpace G := by
  obtain ⟨G₀, i, L₀, hi, -, hirr, hrange, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
      k L
  have hsurj : Function.Surjective i.base := by
    rw [← Set.range_eq_univ]
    show Set.range i = Set.univ
    rw [hrange]
    exact PreconnectedSpace.connectedComponent_eq_univ _
  have h : IsIrreducible (Set.univ : Set G) := by
    have := (IrreducibleSpace.isIrreducible_univ G₀).image i.base i.base.hom.continuous.continuousOn
    rwa [Set.image_univ, Set.range_eq_univ.mpr hsurj] at this
  exact (irreducibleSpace_def G).2 h

theorem eq_of_closure_singleton_eq {X : Type u} [TopologicalSpace X] [T0Space X] {x y : X}
    (h : closure ({x} : Set X) = closure {y}) : x = y := by
  have h₁ : x ⤳ y := specializes_iff_mem_closure.mpr (h ▸ subset_closure rfl)
  have h₂ : y ⤳ x := specializes_iff_mem_closure.mpr (h.symm ▸ subset_closure rfl)
  exact (h₁.antisymm h₂).eq

end General

section Sweep

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)}
  (a : PartialAction k f p)

def sweep (w : P) : Set P :=
  a.hom.base '' ((a.dom.ι ≫ pullback.snd f p).base ⁻¹' closure {w})

theorem sweep_eq_image_closure {w : P} {ζ : ↥(pullback f p)} (hζ : ζ ∈ a.dom)
    (hcl : closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure {w}) :
    sweep a w = a.hom.base '' closure {(⟨ζ, hζ⟩ : ↥(a.dom : Scheme.{u}))} := by
  unfold sweep
  congr 1
  have himg : (a.dom.ι : ↥(a.dom : Scheme.{u}) → ↥(pullback f p)) '' {⟨ζ, hζ⟩} = {ζ} := by
    ext z; simp [Scheme.Opens.ι_apply]
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, ← hcl,
    a.dom.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image]
  congr 2
  exact himg.symm

theorem hom_apply_eq_of_closure_sweep_eq {w w' : P} {ζ : ↥(pullback f p)} (hζ : ζ ∈ a.dom)
    (hcl : closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure {w})
    (hsw : closure (sweep a w) = closure {w'}) :
    a.hom.base ⟨ζ, hζ⟩ = w' := by
  rw [sweep_eq_image_closure a hζ hcl] at hsw
  apply eq_of_closure_singleton_eq
  rw [← hsw]
  apply le_antisymm
  · exact closure_mono (Set.singleton_subset_iff.2 ⟨_, subset_closure rfl, rfl⟩)
  · rw [← closure_closure (s := ({a.hom.base _} : Set P))]
    refine closure_mono ?_
    have h__af := (image_closure_subset_closure_image a.hom.base.hom.continuous
        (s := ({(⟨ζ, hζ⟩ : ↥(a.dom : Scheme.{u}))} : Set _)))
    simp only [Set.image_singleton] at h__af
    exact h__af

theorem sweep_subset {w w' : P} (hsw : closure (sweep a w) = closure {w'}) :
    sweep a w ⊆ closure {w'} :=
  hsw ▸ subset_closure

end Sweep

section API

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)} (a : PartialAction k f p)
  {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec (CommRingCat.of k)}

theorem pair_comp (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (γ : SchemeHomOver t f)
    (x : SchemeHomOver t p) :
    pair (GoodReductionJacobian.schemeHomOverComp ψ hψ γ)
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = ψ ≫ pair γ x := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]; rfl
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]; rfl

theorem defined_comp (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') {γ : SchemeHomOver t f}
    {x : SchemeHomOver t p} (hd : a.Defined γ x) :
    a.Defined (GoodReductionJacobian.schemeHomOverComp ψ hψ γ)
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  unfold Defined
  rw [pair_comp]
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact hd ⟨_, rfl⟩

theorem liftDom_eq {γ : SchemeHomOver t f} {x : SchemeHomOver t p} (hd : a.Defined γ x)
    {g : T ⟶ (a.dom : Scheme.{u})} (hg : g ≫ a.dom.ι = pair γ x) : a.liftDom γ x hd = g := by
  rw [← cancel_mono a.dom.ι, liftDom_ι, hg]

theorem liftDom_comp (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') {γ : SchemeHomOver t f}
    {x : SchemeHomOver t p} (hd : a.Defined γ x) :
    a.liftDom _ _ (defined_comp a ψ hψ hd) = ψ ≫ a.liftDom γ x hd :=
  liftDom_eq a _ (by rw [Category.assoc, liftDom_ι, pair_comp])

theorem act_comp (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') {γ : SchemeHomOver t f}
    {x : SchemeHomOver t p} (hd : a.Defined γ x)
    (hd' : a.Defined (GoodReductionJacobian.schemeHomOverComp ψ hψ γ)
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x)) :
    a.act _ _ hd' = GoodReductionJacobian.schemeHomOverComp ψ hψ (a.act γ x hd) := by
  apply Subtype.ext
  simp only [act_coe, GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc]
  rw [← liftDom_comp a ψ hψ hd]

theorem act_apply {γ : SchemeHomOver t f} {x : SchemeHomOver t p} (hd : a.Defined γ x) (z : T)
    (d : ↥(a.dom : Scheme.{u})) (hdz : a.dom.ι d = pair γ x z) :
    (a.act γ x hd).1 z = a.hom d := by
  rw [act_coe, Scheme.Hom.comp_apply]
  congr 1
  apply a.dom.ι.injective
  rw [hdz, ← Scheme.Hom.comp_apply, liftDom_ι]

theorem mem_dom_of_defined {γ : SchemeHomOver t f} {x : SchemeHomOver t p} (hd : a.Defined γ x)
    (z : T) : pair γ x z ∈ a.dom :=
  hd ⟨z, rfl⟩

end API

section Incidence

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  (L : RelativeGroupLaw k f)
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)} (a : PartialAction k f p)

abbrev R : Scheme.{u} := pullback (pullback.snd f p) a.hom

abbrev tR : R a ⟶ Spec (CommRingCat.of k) :=
  pullback.snd (pullback.snd f p) a.hom ≫ a.dom.ι ≫ pullback.snd f p ≫ p

def γR : SchemeHomOver (tR a) f :=
  ⟨pullback.fst (pullback.snd f p) a.hom ≫ pullback.fst f p, by
    simp only [tR, Category.assoc]
    rw [pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, a.hom_comp]⟩

def δR : SchemeHomOver (tR a) f :=
  ⟨pullback.snd (pullback.snd f p) a.hom ≫ a.dom.ι ≫ pullback.fst f p, by
    simp only [tR, Category.assoc, pullback.condition]⟩

def xR : SchemeHomOver (tR a) p :=
  ⟨pullback.snd (pullback.snd f p) a.hom ≫ a.dom.ι ≫ pullback.snd f p, by
    simp only [tR, Category.assoc]⟩

theorem pair_δR_xR : pair (δR a) (xR a) = pullback.snd (pullback.snd f p) a.hom ≫ a.dom.ι := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst]; rfl
  · rw [pullback.lift_snd]; rfl

theorem defined_δR_xR : a.Defined (δR a) (xR a) := by
  unfold Defined
  rw [pair_δR_xR, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  refine (Set.image_subset_range _ _).trans ?_
  rw [Scheme.Opens.range_ι]

theorem liftDom_δR_xR : a.liftDom (δR a) (xR a) (defined_δR_xR a) =
    pullback.snd (pullback.snd f p) a.hom :=
  liftDom_eq a _ (pair_δR_xR a).symm

theorem act_δR_xR_coe : (a.act (δR a) (xR a) (defined_δR_xR a)).1 =
    pullback.fst (pullback.snd f p) a.hom ≫ pullback.snd f p := by
  rw [act_coe, liftDom_δR_xR, pullback.condition]

theorem pair_γR_act : pair (γR a) (a.act (δR a) (xR a) (defined_δR_xR a)) =
    pullback.fst (pullback.snd f p) a.hom := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst]; rfl
  · rw [pullback.lift_snd, act_δR_xR_coe]

abbrev T₁ : (R a).Opens := pullback.fst (pullback.snd f p) a.hom ⁻¹ᵁ a.dom

abbrev t₁ : (T₁ a : Scheme.{u}) ⟶ Spec (CommRingCat.of k) := (T₁ a).ι ≫ tR a

abbrev γ₁ : SchemeHomOver (t₁ a) f := GoodReductionJacobian.schemeHomOverComp (T₁ a).ι rfl (γR a)
abbrev δ₁ : SchemeHomOver (t₁ a) f := GoodReductionJacobian.schemeHomOverComp (T₁ a).ι rfl (δR a)
abbrev x₁ : SchemeHomOver (t₁ a) p := GoodReductionJacobian.schemeHomOverComp (T₁ a).ι rfl (xR a)

theorem defined₁ : a.Defined (δ₁ a) (x₁ a) := defined_comp a _ _ (defined_δR_xR a)

theorem act₁_eq : a.act (δ₁ a) (x₁ a) (defined₁ a) =
    GoodReductionJacobian.schemeHomOverComp (T₁ a).ι rfl (a.act (δR a) (xR a) (defined_δR_xR a)) :=
  act_comp a _ _ _ _

theorem pair_γ₁_act₁ : pair (γ₁ a) (a.act (δ₁ a) (x₁ a) (defined₁ a)) =
    (T₁ a).ι ≫ pullback.fst (pullback.snd f p) a.hom := by
  rw [act₁_eq, pair_comp, pair_γR_act]

theorem defined₂ : a.Defined (γ₁ a) (a.act (δ₁ a) (x₁ a) (defined₁ a)) := by
  unfold Defined
  rw [pair_γ₁_act₁]
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
  exact z.2

theorem assoc₁ (ha : a.Assoc L) :
    ∃ hd₃ : a.Defined (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a),
      a.act (γ₁ a) (a.act (δ₁ a) (x₁ a) (defined₁ a)) (defined₂ a) =
        a.act (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a) hd₃ :=
  ha (t₁ a) (γ₁ a) (δ₁ a) (x₁ a) (defined₁ a) (defined₂ a)

theorem hom_apply_mem_of_sweep_subset (ha : a.Assoc L) {w : P} {ζ ζ' : ↥(pullback f p)}
    (hζ : ζ ∈ a.dom) (hζw : pullback.snd f p ζ = w) (hζ' : ζ' ∈ a.dom)
    (hζ'w' : pullback.snd f p ζ' = a.hom (⟨ζ, hζ⟩ : ↥(a.dom : Scheme.{u})))
    {W : Set P} (hW : sweep a w ⊆ W) :
    a.hom.base (⟨ζ', hζ'⟩ : ↥(a.dom : Scheme.{u})) ∈ W := by

  obtain ⟨θ, hθ₁, hθ₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd f p)
    (g := a.hom) ζ' ⟨ζ, hζ⟩ hζ'w'
  have hθT : θ ∈ T₁ a := by
    show pullback.fst (pullback.snd f p) a.hom θ ∈ a.dom
    rw [hθ₁]; exact hζ'
  obtain ⟨hd₃, heq⟩ := assoc₁ L a ha

  have hval := congrArg (fun s : SchemeHomOver (t₁ a) p => s.1 (⟨θ, hθT⟩ : ↥(T₁ a))) heq
  simp only at hval

  rw [act_apply a (defined₂ a) ⟨θ, hθT⟩ ⟨ζ', hζ'⟩ (by
    simp only [pair_γ₁_act₁, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, hθ₁])]
    at hval
  rw [hval]

  set d := a.liftDom _ _ hd₃ (⟨θ, hθT⟩ : ↥(T₁ a)) with hd
  rw [act_coe, Scheme.Hom.comp_apply]
  apply hW
  refine ⟨d, ?_, rfl⟩
  show (a.dom.ι ≫ pullback.snd f p) d ∈ closure {w}
  have : (a.dom.ι ≫ pullback.snd f p) d = w := by
    rw [hd, ← Scheme.Hom.comp_apply, ← Category.assoc, liftDom_ι, pullback.lift_snd]
    show ((T₁ a).ι ≫ pullback.snd (pullback.snd f p) a.hom ≫ a.dom.ι ≫ pullback.snd f p) _ = w
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, Scheme.Hom.comp_apply, hθ₂, ← hζw]
    rfl
  rw [this]
  exact subset_closure rfl

end Incidence

section GroupLaw

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  (L : RelativeGroupLaw k f)
  {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec (CommRingCat.of k)}

theorem inv_inv (x : SchemeHomOver t f) : L.inv t (L.inv t x) = x := by
  letI := L.pointGroup t
  exact _root_.inv_inv x

theorem inv_mul_cancel_left (x y : SchemeHomOver t f) : L.mul t (L.inv t x) (L.mul t x y) = y := by
  letI := L.pointGroup t
  exact _root_.inv_mul_cancel_left x y

theorem inv_natural (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) =
      L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural t t' ψ hψ, L.inv_mul_cancel, L.one_natural]
  exact inv_eq_of_mul_eq_one_left h |>.symm

end GroupLaw

section Involution

variable {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f) {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))

abbrev Q : Scheme.{u} := pullback f (pullback.snd f p ≫ p)

abbrev tQ : Q f p ⟶ Spec (CommRingCat.of k) :=
  pullback.snd f (pullback.snd f p ≫ p) ≫ pullback.snd f p ≫ p

def γQ : SchemeHomOver (tQ f p) f :=
  ⟨pullback.fst f (pullback.snd f p ≫ p), by rw [pullback.condition]⟩

def δQ : SchemeHomOver (tQ f p) f :=
  ⟨pullback.snd f (pullback.snd f p ≫ p) ≫ pullback.fst f p, by
    simp only [Category.assoc, pullback.condition]⟩

def xQ : SchemeHomOver (tQ f p) p :=
  ⟨pullback.snd f (pullback.snd f p ≫ p) ≫ pullback.snd f p, by simp only [Category.assoc]⟩

theorem pair_δQ_xQ : pair (δQ f p) (xQ f p) = pullback.snd f (pullback.snd f p ≫ p) := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst]; rfl
  · rw [pullback.lift_snd]; rfl

def ν : Q f p ⟶ Q f p :=
  pullback.lift (L.inv (tQ f p) (γQ f p)).1 (pair (L.mul (tQ f p) (γQ f p) (δQ f p)) (xQ f p)) (by
    rw [(L.inv (tQ f p) (γQ f p)).2, ← Category.assoc, pullback.lift_snd]
    exact (xQ f p).2.symm)

theorem ν_fst : ν f L p ≫ pullback.fst f _ = (L.inv (tQ f p) (γQ f p)).1 := pullback.lift_fst _ _ _

theorem ν_snd : ν f L p ≫ pullback.snd f _ = pair (L.mul (tQ f p) (γQ f p) (δQ f p)) (xQ f p) :=
  pullback.lift_snd _ _ _

theorem ν_snd_snd : ν f L p ≫ pullback.snd f _ ≫ pullback.snd f p =
    pullback.snd f _ ≫ pullback.snd f p := by
  rw [← Category.assoc, ν_snd, pullback.lift_snd]; rfl

theorem ν_tQ : ν f L p ≫ tQ f p = tQ f p := by
  have h := ν_snd_snd f L p
  calc ν f L p ≫ tQ f p
      = (ν f L p ≫ pullback.snd f _ ≫ pullback.snd f p) ≫ p := by simp only [tQ, Category.assoc]
    _ = (pullback.snd f _ ≫ pullback.snd f p) ≫ p := by rw [h]
    _ = tQ f p := by simp only [tQ, Category.assoc]

theorem comp_ν_γQ : GoodReductionJacobian.schemeHomOverComp (ν f L p) (ν_tQ f L p) (γQ f p) =
    L.inv (tQ f p) (γQ f p) :=
  Subtype.ext (ν_fst f L p)

theorem comp_ν_δQ : GoodReductionJacobian.schemeHomOverComp (ν f L p) (ν_tQ f L p) (δQ f p) =
    L.mul (tQ f p) (γQ f p) (δQ f p) := by
  apply Subtype.ext
  change ν f L p ≫ pullback.snd f _ ≫ pullback.fst f p = (L.mul (tQ f p) (γQ f p) (δQ f p)).1
  rw [← Category.assoc, ν_snd, pullback.lift_fst]

theorem comp_ν_xQ : GoodReductionJacobian.schemeHomOverComp (ν f L p) (ν_tQ f L p) (xQ f p) =
    xQ f p := by
  apply Subtype.ext
  change ν f L p ≫ pullback.snd f _ ≫ pullback.snd f p = pullback.snd f _ ≫ pullback.snd f p
  rw [← Category.assoc, ν_snd, pullback.lift_snd]
  rfl

theorem ν_ν : ν f L p ≫ ν f L p = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, ν_fst, Category.id_comp]
    have h1 := inv_natural L (ν f L p) (ν_tQ f L p) (γQ f p)
    rw [comp_ν_γQ, inv_inv] at h1
    exact congrArg Subtype.val h1
  · rw [Category.assoc, ν_snd, Category.id_comp, ← pair_δQ_xQ]
    have hm := L.mul_natural _ _ (ν f L p) (ν_tQ f L p) (γQ f p) (δQ f p)
    rw [comp_ν_γQ, comp_ν_δQ, inv_mul_cancel_left] at hm
    rw [← pair_comp (ν f L p) (ν_tQ f L p), hm, comp_ν_xQ]

scoped instance : IsIso (ν f L p) := ⟨⟨ν f L p, ν_ν f L p, ν_ν f L p⟩⟩

theorem ν_apply_eq_of_closure_eq {Ξ : ↥(Q f p)} {Z : Set P}
    (hΞ : closure ({Ξ} : Set ↥(Q f p)) =
      (pullback.snd f (pullback.snd f p ≫ p) ≫ pullback.snd f p).base ⁻¹' Z) :
    ν f L p Ξ = Ξ := by
  have hS : ∀ z, ν f L p z ∈ closure ({Ξ} : Set ↥(Q f p)) ↔ z ∈ closure ({Ξ} : Set ↥(Q f p)) := by
    intro z
    rw [hΞ, Set.mem_preimage, Set.mem_preimage, ← Scheme.Hom.comp_apply, ν_snd_snd]
  have hinv : ∀ z, ν f L p (ν f L p z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, ν_ν]; rfl
  have himg : (ν f L p).base '' closure {Ξ} = closure {Ξ} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hS y).2 hy
    · intro hz
      have h1 : ν f L p (ν f L p z) ∈ closure ({Ξ} : Set ↥(Q f p)) := by rw [hinv]; exact hz
      exact ⟨ν f L p z, (hS _).1 h1, hinv z⟩
  apply eq_of_closure_singleton_eq
  calc closure {ν f L p Ξ}
      = (ν f L p).homeomorph '' closure {Ξ} := by
        rw [(ν f L p).homeomorph.image_closure, Set.image_singleton]; rfl
    _ = closure {Ξ} := himg

end Involution

section Transport

variable {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f) {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
  (a : PartialAction k f p)

theorem comp_comp {B T'' T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {t'' : T'' ⟶ B}
    {g : A ⟶ B} (φ : T'' ⟶ T') (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (hφ : φ ≫ t' = t'')
    (h : (φ ≫ ψ) ≫ t = t'') (x : SchemeHomOver t g) :
    GoodReductionJacobian.schemeHomOverComp (φ ≫ ψ) h x =
      GoodReductionJacobian.schemeHomOverComp φ hφ (GoodReductionJacobian.schemeHomOverComp ψ hψ x) :=
  Subtype.ext (Category.assoc _ _ _)

def j : R a ⟶ Q f p :=
  (pullbackLeftPullbackSndIso f p a.hom).hom ≫
    pullback.map f (a.hom ≫ p) f (pullback.snd f p ≫ p) (𝟙 G) a.dom.ι (𝟙 _)
      (by simp) (by rw [Category.comp_id, a.hom_comp])

scoped instance : IsOpenImmersion (j f p a) := by
  unfold j; infer_instance

theorem j_fst : j f p a ≫ pullback.fst f _ = pullback.fst _ _ ≫ pullback.fst f p := by
  unfold j
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
    Category.comp_id]

theorem j_snd : j f p a ≫ pullback.snd f _ = pullback.snd _ _ ≫ a.dom.ι := by
  unfold j
  rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullbackLeftPullbackSndIso_hom_snd]

theorem j_tQ : j f p a ≫ tQ f p = tR a := by
  show j f p a ≫ pullback.snd f _ ≫ pullback.snd f p ≫ p = _
  rw [← Category.assoc, j_snd, Category.assoc]

theorem range_j : Set.range (j f p a).base = (pullback.snd f (pullback.snd f p ≫ p)).base ⁻¹' a.dom := by
  unfold j
  rw [Scheme.Hom.comp_base, TopCat.coe_comp,
    (ConcreteCategory.bijective_of_isIso (pullbackLeftPullbackSndIso f p a.hom).hom.base).2.range_comp,
    Scheme.Pullback.range_map]
  simp [Scheme.Opens.range_ι]

theorem comp_j_γQ : GoodReductionJacobian.schemeHomOverComp (j f p a) (j_tQ f p a) (γQ f p) = γR a :=
  Subtype.ext (j_fst f p a)

theorem comp_j_δQ : GoodReductionJacobian.schemeHomOverComp (j f p a) (j_tQ f p a) (δQ f p) = δR a := by
  apply Subtype.ext
  change j f p a ≫ pullback.snd f _ ≫ pullback.fst f p = pullback.snd _ _ ≫ a.dom.ι ≫ pullback.fst f p
  rw [← Category.assoc, j_snd, Category.assoc]

theorem comp_j_xQ : GoodReductionJacobian.schemeHomOverComp (j f p a) (j_tQ f p a) (xQ f p) = xR a := by
  apply Subtype.ext
  change j f p a ≫ pullback.snd f _ ≫ pullback.snd f p = pullback.snd _ _ ≫ a.dom.ι ≫ pullback.snd f p
  rw [← Category.assoc, j_snd, Category.assoc]

variable {hd₃ : a.Defined (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a)}

def Ψ (hd₃ : a.Defined (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a)) : (T₁ a : Scheme.{u}) ⟶ pullback f p :=
  pair (L.inv (t₁ a) (γ₁ a)) (a.act _ _ hd₃)

def ω (hd₃ : a.Defined (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a)) : (T₁ a : Scheme.{u}) ⟶ R a :=
  pullback.lift (Ψ f L p a hd₃) (a.liftDom _ _ hd₃) (by rw [Ψ, pullback.lift_snd, act_coe])

theorem ω_fst (hd₃ : a.Defined (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a)) :
    ω f L p a hd₃ ≫ pullback.fst _ _ = Ψ f L p a hd₃ := pullback.lift_fst _ _ _

theorem ω_snd (hd₃ : a.Defined (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a)) :
    ω f L p a hd₃ ≫ pullback.snd _ _ = a.liftDom _ _ hd₃ := pullback.lift_snd _ _ _

theorem ι_j_tQ : ((T₁ a).ι ≫ j f p a) ≫ tQ f p = t₁ a := by
  rw [Category.assoc, j_tQ]

theorem ω_j (hd₃ : a.Defined (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a)) :
    ω f L p a hd₃ ≫ j f p a = ((T₁ a).ι ≫ j f p a) ≫ ν f L p := by
  have hγ : GoodReductionJacobian.schemeHomOverComp ((T₁ a).ι ≫ j f p a) (ι_j_tQ f p a) (γQ f p) =
      γ₁ a := by
    rw [comp_comp _ _ (j_tQ f p a) rfl, comp_j_γQ]
  have hδ : GoodReductionJacobian.schemeHomOverComp ((T₁ a).ι ≫ j f p a) (ι_j_tQ f p a) (δQ f p) =
      δ₁ a := by
    rw [comp_comp _ _ (j_tQ f p a) rfl, comp_j_δQ]
  have hx : GoodReductionJacobian.schemeHomOverComp ((T₁ a).ι ≫ j f p a) (ι_j_tQ f p a) (xQ f p) =
      x₁ a := by
    rw [comp_comp _ _ (j_tQ f p a) rfl, comp_j_xQ]
  apply pullback.hom_ext
  · rw [Category.assoc, j_fst, ← Category.assoc, ω_fst, Ψ, pullback.lift_fst, Category.assoc, ν_fst]
    have h := inv_natural L ((T₁ a).ι ≫ j f p a) (ι_j_tQ f p a) (γQ f p)
    rw [hγ] at h
    exact (congrArg Subtype.val h).symm
  · rw [Category.assoc, j_snd, ← Category.assoc, ω_snd, liftDom_ι, Category.assoc, ν_snd,
      ← pair_comp _ (ι_j_tQ f p a), L.mul_natural, hγ, hδ, hx]

end Transport

section Generic

variable {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f) {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
  (a : PartialAction k f p)

theorem eq_of_mem_closure_of_mem_closure {X : Type u} [TopologicalSpace X] [T0Space X] {x y : X}
    (h₁ : x ∈ closure ({y} : Set X)) (h₂ : y ∈ closure ({x} : Set X)) : x = y :=
  ((specializes_iff_mem_closure.mpr h₂).antisymm (specializes_iff_mem_closure.mpr h₁)).eq

theorem exists_mem_T₁_Ψ_eq [GeometricallyIrreducible f] [LocallyOfFiniteType f]
    [LocallyOfFiniteType p]
    (hd₃ : a.Defined (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a))
    {w : P} {ζ ζ' : ↥(pullback f p)} (hζ : ζ ∈ a.dom)
    (hζcl : closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure {w})
    (hζ' : ζ' ∈ a.dom)
    (hζ'cl : closure ({ζ'} : Set ↥(pullback f p)) =
      (pullback.snd f p).base ⁻¹' closure {a.hom (⟨ζ, hζ⟩ : ↥(a.dom : Scheme.{u}))})
    (hζ'snd : pullback.snd f p ζ' = a.hom (⟨ζ, hζ⟩ : ↥(a.dom : Scheme.{u}))) :
    ∃ (r : ↥(R a)) (hr : r ∈ T₁ a), Ψ f L p a hd₃ ⟨r, hr⟩ = ζ' ∧
      pullback.snd (pullback.snd f p) a.hom r = ⟨ζ, hζ⟩ := by

  obtain ⟨Ξ, hΞcl, hΞζ, -⟩ :=
    AlgebraicGeometry.exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat f
      (pullback.snd f p ≫ p) ζ
  have hΞM : Ξ ∈ Set.range (j f p a).base := by
    rw [range_j]
    show pullback.snd f _ Ξ ∈ a.dom
    rw [hΞζ]; exact hζ
  obtain ⟨ΞR, hΞR⟩ := hΞM
  have hsndR : pullback.snd (pullback.snd f p) a.hom ΞR = ⟨ζ, hζ⟩ := by
    apply a.dom.ι.injective
    rw [← Scheme.Hom.comp_apply, ← j_snd, Scheme.Hom.comp_apply, hΞR, hΞζ, Scheme.Opens.ι_apply]

  have h1 : pullback.fst (pullback.snd f p) a.hom ΞR ∈ closure ({ζ'} : Set ↥(pullback f p)) := by
    rw [hζ'cl, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
      hsndR]
    exact subset_closure rfl
  obtain ⟨θ, hθ₁, hθ₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd f p)
    (g := a.hom) ζ' ⟨ζ, hζ⟩ hζ'snd
  have hθcl : θ ∈ closure ({ΞR} : Set ↥(R a)) := by
    rw [(j f p a).isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton,
      Set.mem_preimage]
    rw [hΞR, hΞcl, Set.mem_preimage, ← Scheme.Hom.comp_apply, j_snd, Scheme.Hom.comp_apply, hθ₂,
      Scheme.Opens.ι_apply]
    exact subset_closure rfl
  have h2 : ζ' ∈ closure ({pullback.fst (pullback.snd f p) a.hom ΞR} : Set ↥(pullback f p)) := by
    have := image_closure_subset_closure_image
      (pullback.fst (pullback.snd f p) a.hom).base.hom.continuous ⟨θ, hθcl, rfl⟩
    rwa [Set.image_singleton, hθ₁] at this
  have hfst : pullback.fst (pullback.snd f p) a.hom ΞR = ζ' := eq_of_mem_closure_of_mem_closure h1 h2
  have hT : ΞR ∈ T₁ a := by
    show pullback.fst (pullback.snd f p) a.hom ΞR ∈ a.dom
    rw [hfst]; exact hζ'

  have e1 : Ψ f L p a hd₃ ⟨ΞR, hT⟩ =
      pullback.fst (pullback.snd f p) a.hom (ω f L p a hd₃ ⟨ΞR, hT⟩) := by
    rw [← Scheme.Hom.comp_apply, ω_fst]
  have e2 : j f p a (ω f L p a hd₃ ⟨ΞR, hT⟩) = j f p a ΞR := by
    rw [← Scheme.Hom.comp_apply, ω_j, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
      Scheme.Opens.ι_apply]
    change ν f L p (j f p a ΞR) = j f p a ΞR
    rw [hΞR]
    exact ν_apply_eq_of_closure_eq f L p (Z := closure {w}) (by
      rw [hΞcl, hζcl, ← Set.preimage_comp]; rfl)
  have e3 : ω f L p a hd₃ ⟨ΞR, hT⟩ = ΞR := (j f p a).injective e2
  exact ⟨ΞR, hT, by rw [e1, e3, hfst], hsndR⟩

end Generic

section Final

variable {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f) {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
  (a : PartialAction k f p)

theorem stable_of_closure_eq {W : Set P} (hWc : IsClosed W) {ζ' : ↥(pullback f p)} (hζ' : ζ' ∈ a.dom)
    (hcl : closure ({ζ'} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' W)
    (hmem : a.hom (⟨ζ', hζ'⟩ : ↥(a.dom : Scheme.{u})) ∈ W) : a.Stable W := by
  intro z hz
  have hz' : z ∈ closure ({⟨ζ', hζ'⟩} : Set ↥(a.dom : Scheme.{u})) := by
    rw [a.dom.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton,
      Set.mem_preimage, Scheme.Opens.ι_apply, hcl]
    exact hz
  have h := image_closure_subset_closure_image a.hom.base.hom.continuous ⟨z, hz', rfl⟩
  rw [Set.image_singleton] at h
  exact closure_minimal (Set.singleton_subset_iff.2 hmem) hWc h

theorem act_congr {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
    {x x' : SchemeHomOver t p} (h : x = x') (hd : a.Defined γ x) (hd' : a.Defined γ x') :
    a.act γ x hd = a.act γ x' hd' := by
  subst h; rfl

theorem exists_rational_defined_one [IsAlgClosed k] [LocallyOfFiniteType (tR a)] (ha : a.Assoc L)
    (hd₃ : a.Defined (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a))
    (heq : a.act (γ₁ a) (a.act (δ₁ a) (x₁ a) (defined₁ a)) (defined₂ a) =
      a.act (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a) hd₃)
    {r : ↥(R a)} (hr : r ∈ T₁ a) (hΨr : Ψ f L p a hd₃ ⟨r, hr⟩ ∈ a.dom) {w : P}
    (hrw : (pullback.snd (pullback.snd f p) a.hom ≫ a.dom.ι ≫ pullback.snd f p) r ∈ closure {w})
    {W : Set P} (hW : sweep a w ⊆ W) :
    ∃ P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p,
      P₀.1 (IsLocalRing.closedPoint k) ∈ W ∧
      a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀ := by

  let T₃ : (T₁ a : Scheme.{u}).Opens := Ψ f L p a hd₃ ⁻¹ᵁ a.dom
  let A : Set ↥(R a) := ((T₁ a).ι ''ᵁ T₃ : Set ↥(R a)) ∩
    (pullback.snd (pullback.snd f p) a.hom ≫ a.dom.ι ≫ pullback.snd f p).base ⁻¹' closure {w}
  have hA : IsLocallyClosed A :=
    ((T₁ a).ι ''ᵁ T₃).isOpen.isLocallyClosed.inter
      (isClosed_closure.preimage (Scheme.Hom.continuous _)).isLocallyClosed
  have hAne : A.Nonempty := ⟨r, ⟨⟨r, hr⟩, hΨr, rfl⟩, hrw⟩
  haveI : JacobsonSpace ↥(R a) := AlgebraicGeometry.jacobsonSpace_of_locallyOfFiniteType (tR a)
  obtain ⟨t, ⟨⟨t₁', ht₃, ht₁⟩, htw⟩, htc⟩ := nonempty_inter_closedPoints hAne hA
  obtain ⟨τ, hτ, hτt⟩ :=
    AlgebraicGeometry.Scheme.exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton (tR a) k t htc
  have hτ1 : τ ≫ tR a = 𝟙 _ := by
    rw [hτ, Algebra.algebraMap_self]
    exact Spec.map_id _

  have hτT : Set.range τ.base ⊆ Set.range (T₁ a).ι.base := by
    rintro _ ⟨z, rfl⟩
    obtain rfl : z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    exact ⟨t₁', ht₁.trans hτt.symm⟩
  let τ₁ : Spec (CommRingCat.of k) ⟶ (T₁ a : Scheme.{u}) := IsOpenImmersion.lift (T₁ a).ι τ hτT
  have hτ₁ : τ₁ ≫ (T₁ a).ι = τ := IsOpenImmersion.lift_fac _ _ _
  have hτ₁t : τ₁ (IsLocalRing.closedPoint k) = t₁' := by
    apply (T₁ a).ι.injective
    rw [← Scheme.Hom.comp_apply, hτ₁, hτt]
    exact ht₁.symm
  have hs : τ₁ ≫ t₁ a = 𝟙 _ := by
    show τ₁ ≫ (T₁ a).ι ≫ tR a = 𝟙 _
    rw [← Category.assoc, hτ₁, hτ1]

  have hd01 : a.Defined (GoodReductionJacobian.schemeHomOverComp τ₁ hs (δ₁ a))
      (GoodReductionJacobian.schemeHomOverComp τ₁ hs (x₁ a)) := defined_comp a τ₁ hs (defined₁ a)
  have hy : a.act _ _ hd01 =
      GoodReductionJacobian.schemeHomOverComp τ₁ hs (a.act (δ₁ a) (x₁ a) (defined₁ a)) :=
    act_comp a τ₁ hs (defined₁ a) hd01
  have hd02' : a.Defined (GoodReductionJacobian.schemeHomOverComp τ₁ hs (γ₁ a))
      (GoodReductionJacobian.schemeHomOverComp τ₁ hs (a.act (δ₁ a) (x₁ a) (defined₁ a))) :=
    defined_comp a τ₁ hs (defined₂ a)
  have hd02 : a.Defined (GoodReductionJacobian.schemeHomOverComp τ₁ hs (γ₁ a)) (a.act _ _ hd01) := by
    rw [hy]; exact hd02'
  have hact2 : a.act _ _ hd02 = GoodReductionJacobian.schemeHomOverComp τ₁ hs
      (a.act (γ₁ a) (a.act (δ₁ a) (x₁ a) (defined₁ a)) (defined₂ a)) := by
    rw [act_congr f p a _ hy hd02 hd02']
    exact act_comp a τ₁ hs (defined₂ a) hd02'

  have hd0inv : a.Defined (L.inv _ (GoodReductionJacobian.schemeHomOverComp τ₁ hs (γ₁ a)))
      (a.act _ _ hd02) := by
    have hp : pair (L.inv _ (GoodReductionJacobian.schemeHomOverComp τ₁ hs (γ₁ a))) (a.act _ _ hd02) =
        τ₁ ≫ Ψ f L p a hd₃ := by
      rw [hact2, heq, ← inv_natural L τ₁ hs (γ₁ a), pair_comp]
      rfl
    unfold Defined
    rw [hp]
    rintro _ ⟨z, rfl⟩
    obtain rfl : z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [Scheme.Hom.comp_apply, hτ₁t]
    exact ht₃
  obtain ⟨hd0e, -⟩ := ha _ (L.inv _ (GoodReductionJacobian.schemeHomOverComp τ₁ hs (γ₁ a)))
    (GoodReductionJacobian.schemeHomOverComp τ₁ hs (γ₁ a)) (a.act _ _ hd01) hd02 hd0inv
  rw [L.inv_mul_cancel] at hd0e
  refine ⟨a.act _ _ hd01, ?_, hd0e⟩

  rw [hy, GoodReductionJacobian.schemeHomOverComp_coe, act₁_eq,
    GoodReductionJacobian.schemeHomOverComp_coe, act_δR_xR_coe, ← Category.assoc, hτ₁,
    Scheme.Hom.comp_apply, hτt, pullback.condition, Scheme.Hom.comp_apply]
  apply hW
  refine ⟨_, ?_, rfl⟩
  rw [Set.mem_preimage, Scheme.Hom.comp_apply] at htw
  exact htw

end Final

end GoodReductionJacobian.PartialAction.SweptDivisorB1e
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_exists_stable_defined_one_of_closure_image_eq_closure_singleton.GoodReductionJacobian P2MW.S_GoodReductionJacobian_PartialAction_exists_stable_defined_one_of_closure_image_eq_closure_singleton.GoodReductionJacobian.PartialAction P2MW.S_GoodReductionJacobian_PartialAction_exists_stable_defined_one_of_closure_image_eq_closure_singleton.GoodReductionJacobian.PartialAction.SweptDivisorB1e"
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_exists_stable_defined_one_of_closure_image_eq_closure_singleton.GoodReductionJacobian P2MW.S_GoodReductionJacobian_PartialAction_exists_stable_defined_one_of_closure_image_eq_closure_singleton.GoodReductionJacobian.PartialAction"
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_exists_stable_defined_one_of_closure_image_eq_closure_singleton.GoodReductionJacobian"

open GoodReductionJacobian.PartialAction.SweptDivisorB1e in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsProper p] [IsIntegral P]
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L)
    (hcod : ∀ z : ↥(pullback f p), ringKrullDim ((pullback f p).presheaf.stalk z) ≤ 1 → z ∈ a.dom)
    (w w' : P) (hw₁ : ringKrullDim (P.presheaf.stalk w) = 1)
    (hw'₁ : ringKrullDim (P.presheaf.stalk w') = 1)
    (hsw : closure (a.hom.base '' ((a.dom.ι ≫ pullback.snd f p).base ⁻¹' closure {w})) =
      closure {w'}) :
    ∃ P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p,
      topologicalKrullDim ↥(closure {w'}) + 1 ≤ topologicalKrullDim ↥P ∧
      a.Stable (closure {w'}) ∧
      P₀.1 (IsLocalRing.closedPoint k) ∈ closure {w'} ∧
      a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀ := by
  haveI : IrreducibleSpace G := irreducibleSpace_of_connected L
  haveI : GeometricallyIrreducible f :=
    AlgebraicGeometry.GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed f

  obtain ⟨ζ, hζcl, hζw, hζdim⟩ :=
    AlgebraicGeometry.exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat f p w
  have hζ : ζ ∈ a.dom := hcod ζ (hζdim.trans hw₁).le
  have hWsub : sweep a w ⊆ closure {w'} := sweep_subset a hsw
  have hw'eq : a.hom.base (⟨ζ, hζ⟩ : ↥(a.dom : Scheme.{u})) = w' :=
    hom_apply_eq_of_closure_sweep_eq a hζ hζcl hsw

  obtain ⟨ζ', hζ'cl, hζ'w', hζ'dim⟩ :=
    AlgebraicGeometry.exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat f p w'
  have hζ' : ζ' ∈ a.dom := hcod ζ' (hζ'dim.trans hw'₁).le
  have hmem : a.hom (⟨ζ', hζ'⟩ : ↥(a.dom : Scheme.{u})) ∈ closure ({w'} : Set P) :=
    hom_apply_mem_of_sweep_subset L a ha hζ hζw hζ' (by rw [hζ'w', hw'eq]) hWsub
  have hstab : a.Stable (closure {w'}) := stable_of_closure_eq f p a isClosed_closure hζ' hζ'cl hmem

  obtain ⟨hd₃, heq⟩ := assoc₁ L a ha
  obtain ⟨r, hr, hΨ, hrsnd⟩ := exists_mem_T₁_Ψ_eq f L p a hd₃ hζ hζcl hζ'
    (by rw [hw'eq]; exact hζ'cl) (by rw [hw'eq]; exact hζ'w')
  obtain ⟨P₀, hP₀W, hP₀e⟩ := exists_rational_defined_one f L p a ha hd₃ heq hr
    (by rw [hΨ]; exact hζ') (w := w) (by
      rw [Scheme.Hom.comp_apply, hrsnd, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, hζw]
      exact subset_closure rfl) hWsub
  exact ⟨P₀, dim_closure_add_one_le p w' hw'₁, hstab, hP₀W, hP₀e⟩

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_exists_stable_defined_one_of_closure_image_eq_closure_singleton.GoodReductionJacobian P2MW.S_GoodReductionJacobian_PartialAction_exists_stable_defined_one_of_closure_image_eq_closure_singleton.GoodReductionJacobian.PartialAction P2MW.S_GoodReductionJacobian_PartialAction_exists_stable_defined_one_of_closure_image_eq_closure_singleton.GoodReductionJacobian.PartialAction.SweptDivisorB1e"

end S_GoodReductionJacobian_PartialAction_exists_stable_defined_one_of_closure_image_eq_closure_singleton
end P2MW
export P2MW.S_GoodReductionJacobian_PartialAction_exists_stable_defined_one_of_closure_image_eq_closure_singleton (solution)
