-- Prove2me | solution 1 for ModularCurve.exists_addMonoidHom_points_finitePart_eq_finPts_jHNeronObjectAtP_of_closedImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/362ad54c-56de-5953-bcf3-2eeecbe8a238

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification

import Theorems.Thm_ModularCurve_JHNeronObjectAtP_mem_finPts_iff_and_isTorsionPoint_section_and_specialPt
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_toricPts_le_torsion
import Theorems.Thm_ValuationSubring_algHom_apply_mem_of_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_addMonoidHom_points_finitePart_eq_finPts_jHNeronObjectAtP_of_closedImmersion

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

namespace TPts

open PDivisibleGroup ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

universe u

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem exists_comp_eq_of_isOpenImmersion_of_closedPoint_mem
    {O : Type u} [CommRing O] [IsLocalRing O] {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (σ : Spec (CommRingCat.of O) ⟶ Y) (h : σ.base (IsLocalRing.closedPoint O) ∈ Set.range j.base) :
    ∃ τ : Spec (CommRingCat.of O) ⟶ U, τ ≫ j = σ := by
  have hsub : Set.range σ.base ⊆ Set.range j.base := by
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map σ.base.hom.continuous).mem_open j.isOpenEmbedding.isOpen_range h
  exact ⟨IsOpenImmersion.lift j σ hsub, IsOpenImmersion.lift_fac j σ hsub⟩

theorem specMap_ofHom_inj {A B : Type u} [CommRing A] [CommRing B] {f g : A →+* B}
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g := by
  have := Spec.map_injective h
  simpa using congrArg CommRingCat.Hom.hom this

theorem specMap_ofHom_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_eq_specMap_ofHom {A B : Type u} [CommRing A] [CommRing B]
    (φ : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) : ∃ f : A →+* B, φ = Spec.map (CommRingCat.ofHom f) :=
  ⟨(Spec.preimage φ).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩

section RGL

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)

theorem nsmul_coe {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (s : SchemeHomOver t f) :
    (G.nsmul t n s).1 = s.1 ≫ G.schemeNsmul n := by
  have hs : GoodReductionJacobian.schemeHomOverComp s.1 s.2 (RelativeGroupLaw.idPoint (f := f)) = s :=
    Subtype.ext (Category.comp_id _)
  have := G.nsmul_natural f t s.1 s.2 n RelativeGroupLaw.idPoint
  rw [hs] at this
  rw [← this]
  rfl

theorem one_coe {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).1 = t ≫ (G.one (𝟙 _)).1 := by
  rw [← G.one_natural (𝟙 _) t t (Category.comp_id _)]
  rfl

theorem coe_comp_schemeNsmul_of_isTorsionPoint {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (s : SchemeHomOver t f) (hs : G.IsTorsionPoint t n s) :
    s.1 ≫ G.schemeNsmul n = (s.1 ≫ f) ≫ (G.one (𝟙 _)).1 := by
  rw [← nsmul_coe, hs, one_coe, s.2]

theorem mul_coe_cast {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (e : t = t')
    (x y : SchemeHomOver t f) (hx : x.1 ≫ f = t') (hy : y.1 ≫ f = t') :
    (G.mul t' ⟨x.1, hx⟩ ⟨y.1, hy⟩).1 = (G.mul t x y).1 := by
  subst e; rfl

end RGL

section Frame

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {Pl : ValuationSubring ℚ̄} {hPl : Pl.LiesOverPrime p}
  [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM Pl}
  (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)
  {Rh : Type} [CommRing Rh] [Algebra Rh ℚ̄]
  {h : ℕ} (𝒢 : PDivisibleGroup Rh p h)
  (ρh : XHDRLevel.R p →+* Rh)
  (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)

noncomputable abbrev rh {v : ℕ} (x : 𝒢.Point ℚ̄ v) : 𝒢.level v →+* ℚ̄ :=
  ((Point.toAlgHom x : 𝒢.level v →ₐ[Rh] ℚ̄) : 𝒢.level v →+* ℚ̄)

theorem rh_comp_algebraMap {v : ℕ} (x : 𝒢.Point ℚ̄ v) : (rh 𝒢 x).comp (algebraMap Rh (𝒢.level v)) = algebraMap Rh ℚ̄ :=
  (Point.toAlgHom x).comp_algebraMap

noncomputable def P (v : ℕ) (x : 𝒢.Point ℚ̄ v) : Spec (CommRingCat.of ℚ̄) ⟶ O.G :=
  Spec.map (CommRingCat.ofHom (rh 𝒢 x)) ≫ ι v

variable (hρh : (algebraMap Rh ℚ̄).comp ρh = algebraMap (XHDRLevel.R p) ℚ̄)
  (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))

include hρh in
theorem genPt_eq : Spec.map (CommRingCat.ofHom (algebraMap Rh ℚ̄)) ≫ Spec.map (CommRingCat.ofHom ρh) = genPt p := by
  rw [specMap_ofHom_comp, hρh]

include hρh hιbase in
theorem P_comp_g (v : ℕ) (x : 𝒢.Point ℚ̄ v) : P O 𝒢 ι v x ≫ O.g = genPt p := by
  rw [P, Category.assoc, hιbase, ← Category.assoc, specMap_ofHom_comp, rh_comp_algebraMap, genPt_eq ρh hρh]

noncomputable def pt (v : ℕ) (x : 𝒢.Point ℚ̄ v) : SchemeHomOver (genPt p) O.g :=
  ⟨P O 𝒢 ι v x, P_comp_g O 𝒢 ρh ι hρh hιbase v x⟩

noncomputable def δ (v : ℕ) (x : 𝒢.Point ℚ̄ v) : JH M H :=
  O.pts.symm (pt O 𝒢 ρh ι hρh hιbase v x)

theorem pts_δ (v : ℕ) (x : 𝒢.Point ℚ̄ v) : O.pts (δ O 𝒢 ρh ι hρh hιbase v x) = pt O 𝒢 ρh ι hρh hιbase v x :=
  O.pts.apply_symm_apply _

theorem pts_δ_coe (v : ℕ) (x : 𝒢.Point ℚ̄ v) :
    (O.pts (δ O 𝒢 ρh ι hρh hιbase v x)).1 = Spec.map (CommRingCat.ofHom (rh 𝒢 x)) ≫ ι v := by
  rw [pts_δ]; rfl

theorem eq_of_pts_coe_eq {a b : JH M H} (hab : (O.pts a).1 = (O.pts b).1) : a = b :=
  O.pts.injective (Subtype.ext hab)

variable
  (hιmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)

include hιmul in
theorem δ_mul (v : ℕ) (x y : 𝒢.Point ℚ̄ v) :
    δ O 𝒢 ρh ι hρh hιbase v (x * y) = δ O 𝒢 ρh ι hρh hιbase v x + δ O 𝒢 ρh ι hρh hιbase v y := by
  apply O.pts.injective
  rw [O.pts_add, pts_δ, pts_δ, pts_δ]
  apply Subtype.ext
  have hx : (Spec.map (CommRingCat.ofHom (rh 𝒢 x)) ≫ ι v) ≫ O.g =
      Spec.map (CommRingCat.ofHom (algebraMap Rh ℚ̄)) ≫ Spec.map (CommRingCat.ofHom ρh) := by
    rw [genPt_eq ρh hρh]; exact P_comp_g O 𝒢 ρh ι hρh hιbase v x
  have hy : (Spec.map (CommRingCat.ofHom (rh 𝒢 y)) ≫ ι v) ≫ O.g =
      Spec.map (CommRingCat.ofHom (algebraMap Rh ℚ̄)) ≫ Spec.map (CommRingCat.ofHom ρh) := by
    rw [genPt_eq ρh hρh]; exact P_comp_g O 𝒢 ρh ι hρh hιbase v y
  have key := hιmul v ℚ̄ x y hx hy
  change Spec.map (CommRingCat.ofHom (rh 𝒢 (x * y))) ≫ ι v = _
  rw [key]
  exact mul_coe_cast O.L (genPt_eq ρh hρh).symm (pt O 𝒢 ρh ι hρh hιbase v x) (pt O 𝒢 ρh ι hρh hιbase v y) hx hy

noncomputable def δAdd (v : ℕ) : Additive (𝒢.Point ℚ̄ v) →+ JH M H :=
  AddMonoidHom.mk' (fun x => δ O 𝒢 ρh ι hρh hιbase v (Additive.toMul x))
    (fun x y => by rw [toMul_add, δ_mul O 𝒢 ρh ι hρh hιbase hιmul])

@[scoped simp] theorem δAdd_apply (v : ℕ) (x : 𝒢.Point ℚ̄ v) :
    δAdd O 𝒢 ρh ι hρh hιbase hιmul v (Additive.ofMul x) = δ O 𝒢 ρh ι hρh hιbase v x := rfl

end Frame

end TPts
p2m_reactivate "P2MW.S_ModularCurve_exists_addMonoidHom_points_finitePart_eq_finPts_jHNeronObjectAtP_of_closedImmersion.TPts"

namespace TPts

open PDivisibleGroup ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

local notation "ℚ̄" => AlgebraicClosure ℚ

section Frame2

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {Pl : ValuationSubring ℚ̄} {hPl : Pl.LiesOverPrime p}
  [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM Pl}
  (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)
  {Rh : Type} [CommRing Rh] [Algebra Rh ℚ̄]
  {h : ℕ} (𝒢 : PDivisibleGroup Rh p h)
  (ρh : XHDRLevel.R p →+* Rh)
  (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
  (hρh : (algebraMap Rh ℚ̄).comp ρh = algebraMap (XHDRLevel.R p) ℚ̄)
  (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
  (hιmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
  (hιt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v)) ≫ ι (v + 1) = ι v)

include hιt in
theorem δ_pointIncl (v : ℕ) (x : 𝒢.Point ℚ̄ v) :
    δ O 𝒢 ρh ι hρh hιbase (v + 1) (𝒢.pointIncl ℚ̄ v x) = δ O 𝒢 ρh ι hρh hιbase v x := by
  apply eq_of_pts_coe_eq O
  have hr : rh 𝒢 (𝒢.pointIncl ℚ̄ v x) = (rh 𝒢 x).comp (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v) :=
    RingHom.ext fun _ => rfl
  rw [pts_δ_coe, pts_δ_coe, hr, ← specMap_ofHom_comp, Category.assoc, hιt]

include hιt in
theorem δ_pointInclLE {v w : ℕ} (hvw : v ≤ w) (x : 𝒢.Point ℚ̄ v) :
    δ O 𝒢 ρh ι hρh hιbase w (𝒢.pointInclLE ℚ̄ hvw x) = δ O 𝒢 ρh ι hρh hιbase v x := by
  induction hvw with
  | refl => rw [𝒢.pointInclLE_self]
  | step hvw ih => rw [𝒢.pointInclLE_succ hvw, δ_pointIncl O 𝒢 ρh ι hρh hιbase hιt, ih]

noncomputable def Δ : 𝒢.Points ℚ̄ →+ JH M H :=
  AddCommGroup.DirectLimit.lift (fun v => Additive (𝒢.Point ℚ̄ v)) (fun v w hvw => 𝒢.pointsDirectedSystemMap v w hvw)
    (JH M H) (fun v => δAdd O 𝒢 ρh ι hρh hιbase hιmul v) (fun v w hvw x => by
      change δ O 𝒢 ρh ι hρh hιbase w (𝒢.pointInclLE ℚ̄ hvw (Additive.toMul x)) = δ O 𝒢 ρh ι hρh hιbase v (Additive.toMul x)
      exact δ_pointInclLE O 𝒢 ρh ι hρh hιbase hιt hvw (Additive.toMul x))

theorem Δ_mkAdd (v : ℕ) (x : 𝒢.Point ℚ̄ v) :
    Δ O 𝒢 ρh ι hρh hιbase hιmul hιt (𝒢.pointsMkAdd ℚ̄ v (Additive.ofMul x)) = δ O 𝒢 ρh ι hρh hιbase v x := by
  unfold Δ PDivisibleGroup.pointsMkAdd
  erw [AddCommGroup.DirectLimit.lift_of (G := fun v => Additive (𝒢.Point ℚ̄ v))
    (f := fun v w hvw => 𝒢.pointsDirectedSystemMap v w hvw) (JH M H)
    (fun v => δAdd O 𝒢 ρh ι hρh hιbase hιmul v) _ v (Additive.ofMul x)]
  rfl

variable
  (hιcl : ∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h1))

include hιcl in
theorem δ_injective (v : ℕ) : Function.Injective (δ O 𝒢 ρh ι hρh hιbase v) := by
  intro x y hxy
  have h1 : Spec.map (CommRingCat.ofHom (rh 𝒢 x)) ≫ ι v = Spec.map (CommRingCat.ofHom (rh 𝒢 y)) ≫ ι v := by
    rw [← pts_δ_coe O 𝒢 ρh ι hρh hιbase, ← pts_δ_coe O 𝒢 ρh ι hρh hιbase, hxy]
  haveI := hιcl v (hιbase v)
  have h2 : Spec.map (CommRingCat.ofHom (rh 𝒢 x)) ≫ pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) (hιbase v) =
      Spec.map (CommRingCat.ofHom (rh 𝒢 y)) ≫ pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) (hιbase v) := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using h1
    · simp only [Category.assoc, pullback.lift_snd, specMap_ofHom_comp, rh_comp_algebraMap]
  have h3 := specMap_ofHom_inj ((cancel_mono _).1 h2)
  exact Point.ext fun a => DFunLike.congr_fun h3 a

include hιcl in
theorem Δ_injective : Function.Injective (Δ O 𝒢 ρh ι hρh hιbase hιmul hιt) := by
  intro z w hzw
  induction z using Points.induction_on with
  | ih v x =>
    induction w using Points.induction_on with
    | ih w y =>
      rw [← 𝒢.pointsMkAdd_pointInclLE (le_max_left v w) x, ← 𝒢.pointsMkAdd_pointInclLE (le_max_right v w) y] at hzw ⊢
      rw [Δ_mkAdd, Δ_mkAdd] at hzw
      rw [δ_injective O 𝒢 ρh ι hρh hιbase hιcl _ hzw]

theorem Δ_galois (τ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (τ' : ℚ̄ ≃ₐ[Rh] ℚ̄) (hτ : ∀ x : ℚ̄, τ' x = τ x) (z : 𝒢.Points ℚ̄) :
    Δ O 𝒢 ρh ι hρh hιbase hιmul hιt (τ' • z) = τ • Δ O 𝒢 ρh ι hρh hιbase hιmul hιt z := by
  induction z using Points.induction_on with
  | ih v x =>
    rw [Points.smul_pointsMkAdd, Δ_mkAdd, Δ_mkAdd]
    apply eq_of_pts_coe_eq O
    have hr : rh 𝒢 (𝒢.pointMap (τ' : ℚ̄ →ₐ[Rh] ℚ̄) v x) = (τ : ℚ̄ →+* ℚ̄).comp (rh 𝒢 x) :=
      RingHom.ext fun a => hτ _
    rw [pts_δ_coe, O.pts_galois, pts_δ_coe, hr, ← specMap_ofHom_comp, Category.assoc]

theorem Δ_hecke (S : Set ℕ) (g : CohCarrier.Gen M S) (φ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v)
    (hφ : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (φ v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v = ι v ≫ (O.hecke S g).1)
    (v : ℕ) (x : 𝒢.Point ℚ̄ v) :
    Δ O 𝒢 ρh ι hρh hιbase hιmul hιt (𝒢.pointsMkAdd ℚ̄ v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
      ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) =
      genOpH M H S g (Δ O 𝒢 ρh ι hρh hιbase hιmul hιt (𝒢.pointsMkAdd ℚ̄ v (Additive.ofMul x))) := by
  rw [Δ_mkAdd, Δ_mkAdd]
  apply eq_of_pts_coe_eq O
  have hr : rh 𝒢 (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[Rh] 𝒢.level v))) =
      (rh 𝒢 x).comp (φ v : 𝒢.level v →+* 𝒢.level v) :=
    RingHom.ext fun _ => rfl
  rw [pts_δ_coe, O.hecke_pts, pts_δ_coe, hr, ← specMap_ofHom_comp, Category.assoc, hφ, Category.assoc]

end Frame2
p2m_reactivate "P2MW.S_ModularCurve_exists_addMonoidHom_points_finitePart_eq_finPts_jHNeronObjectAtP_of_closedImmersion.TPts"

end TPts
p2m_reactivate "P2MW.S_ModularCurve_exists_addMonoidHom_points_finitePart_eq_finPts_jHNeronObjectAtP_of_closedImmersion.TPts"

namespace TPts

open PDivisibleGroup ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

local notation "ℚ̄" => AlgebraicClosure ℚ

section Place

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {Pl : ValuationSubring ℚ̄} {hPl : Pl.LiesOverPrime p}
  [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM Pl}
  (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)

omit [Fact p.Prime] [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)] in

theorem σA_eq_specMap (φ : XHDRLevel.R p →+* Pl) (hφ : Pl.subtype.comp φ = algebraMap (XHDRLevel.R p) ℚ̄) :
    Λ.σA = Spec.map (CommRingCat.ofHom φ) := by
  obtain ⟨ψ, hψ⟩ := exists_eq_specMap_ofHom Λ.σA
  have hσ : barPt Pl ≫ Λ.σA = genPt p := Λ.hσA
  rw [hψ] at hσ ⊢
  have hσ' : Pl.subtype.comp ψ = algebraMap (XHDRLevel.R p) ℚ̄ := specMap_ofHom_inj (by
    rw [← specMap_ofHom_comp]; exact hσ)
  congr 2
  exact RingHom.ext fun r => Subtype.val_injective (DFunLike.congr_fun (hσ'.trans hφ.symm) r)

omit [Fact p.Prime] [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)] in
theorem barPt_comp_specMap {B : Type} [CommRing B] (f : B →+* Pl) :
    barPt Pl ≫ Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom (Pl.subtype.comp f)) :=
  specMap_ofHom_comp _ _

theorem toricPoint_mem_finPts (m : ℕ) (hm : 0 < m)
    (χ : muCoord ↥Pl O.toricRank m →ₐ[↥Pl] ℚ̄) : O.toricPoint m hm χ ∈ O.finPts m := by
  haveI : NeZero m := ⟨hm.ne'⟩
  rw [(ModularCurve.JHNeronObjectAtP.mem_finPts_iff_and_isTorsionPoint_section_and_specialPt p M H hpM Pl hPl Λ O m).1]
  refine ⟨ModularCurve.JHNeronObjectAtP.toricPts_le_torsion p M H hpM Pl hPl Λ O m ?_, ?_⟩
  · rw [JHNeronObjectAtP.toricPts, dif_pos hm]
    exact AddSubgroup.subset_closure ⟨χ, rfl⟩
  · have hχ : ∀ a, χ a ∈ Pl := ValuationSubring.algHom_apply_mem_of_moduleFinite Pl (fun r : ↥Pl => r.2) χ
    let χPl : muCoord ↥Pl O.toricRank m →+* ↥Pl := (χ : muCoord ↥Pl O.toricRank m →+* ℚ̄).codRestrict Pl hχ
    have hχPl : χPl.comp (algebraMap ↥Pl (muCoord ↥Pl O.toricRank m)) = RingHom.id ↥Pl :=
      RingHom.ext fun r => Subtype.val_injective (χ.commutes r)
    refine ⟨⟨Spec.map (CommRingCat.ofHom χPl) ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA, ?_⟩, ?_⟩
    · have h2 : (O.toricLift m hm).1 ≫ pullback.snd O.g Λ.σA = muStr ↥Pl O.toricRank m := (O.toricLift m hm).2
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (O.toricLift m hm).1, h2,
        ← Category.assoc]
      change (Spec.map (CommRingCat.ofHom χPl) ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥Pl (muCoord ↥Pl O.toricRank m)))) ≫ Λ.σA = Λ.σA
      rw [specMap_ofHom_comp, hχPl, CommRingCat.ofHom_id]
      erw [Spec.map_id]
      exact Category.id_comp _
    · rw [JHNeronObjectAtP.toricPoint, Equiv.apply_symm_apply]
      change ((muPt Pl O.toricRank m χ).1 ≫ (O.toricLift m hm).1) ≫ pullback.fst O.g Λ.σA =
        barPt Pl ≫ Spec.map (CommRingCat.ofHom χPl) ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA
      rw [← Category.assoc (barPt Pl), barPt_comp_specMap]
      rfl

theorem toricPts_le_finPts (m : ℕ) : O.toricPts m ≤ O.finPts m := by
  by_cases hm : 0 < m
  · rw [JHNeronObjectAtP.toricPts, dif_pos hm, AddSubgroup.closure_le]
    rintro _ ⟨χ, rfl⟩
    exact toricPoint_mem_finPts O m hm χ
  · rw [JHNeronObjectAtP.toricPts, dif_neg hm]
    exact bot_le

variable
  {Rh : Type} [CommRing Rh] [IsLocalRing Rh] [Algebra Rh ℚ̄]
  (hRA : ∀ x : Rh, algebraMap Rh ℚ̄ x ∈ Pl)
  (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh ℚ̄ x) < 1)
  {h : ℕ} (𝒢 : PDivisibleGroup Rh p h)
  (ρh : XHDRLevel.R p →+* Rh)
  (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
  (hρh : (algebraMap Rh ℚ̄).comp ρh = algebraMap (XHDRLevel.R p) ℚ̄)
  (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
  (hιmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
  (hιp : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
  (hιfin : ∀ (v : ℕ)
      (h3 : ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρh))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρh))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρh))).base x = IsLocalRing.closedPoint Rh →
          x ∈ Set.range jv.base)

noncomputable def rPl : Rh →+* ↥Pl := (algebraMap Rh ℚ̄).codRestrict Pl hRA

omit [IsLocalRing Rh] in
theorem subtype_comp_rPl : Pl.subtype.comp (rPl hRA) = algebraMap Rh ℚ̄ := RingHom.ext fun _ => rfl

include hρh in
omit [IsLocalRing Rh] in
theorem σA_eq : Spec.map (CommRingCat.ofHom (rPl hRA)) ≫ Spec.map (CommRingCat.ofHom ρh) = Λ.σA := by
  rw [specMap_ofHom_comp, σA_eq_specMap (Λ := Λ) ((rPl hRA).comp ρh) (by rw [← RingHom.comp_assoc, subtype_comp_rPl, hρh])]

include hRloc in
theorem isLocalHom_rPl : IsLocalHom (rPl (Pl := Pl) hRA) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have h1 : a ∈ maximalIdeal Rh := (IsLocalRing.mem_maximalIdeal a).2 (mem_nonunits_iff.2 hna)
  have h2 := (hRloc a).1 h1
  have h3 := (Pl.valuation_eq_one_iff (rPl hRA a)).1 ha
  exact (ne_of_lt h2) h3

include hRA hιmul in

theorem δ_mem_finPts (v : ℕ) (x : 𝒢.Point ℚ̄ v) : δ O 𝒢 ρh ι hρh hιbase v x ∈ O.finPts (p ^ v) := by
  rw [(ModularCurve.JHNeronObjectAtP.mem_finPts_iff_and_isTorsionPoint_section_and_specialPt p M H hpM Pl hPl Λ O (p ^ v)).1]
  refine ⟨?_, ?_⟩
  · rw [Pic0.mem_torsion, natCast_zsmul, ← δAdd_apply O 𝒢 ρh ι hρh hιbase hιmul, ← map_nsmul, ← ofMul_pow,
      Point.pow_card_eq_one, ofMul_one, map_zero]
  · let xPl : 𝒢.level v →+* ↥Pl := (rh 𝒢 x).codRestrict Pl
      (fun a => ValuationSubring.algHom_apply_mem_of_moduleFinite Pl hRA (Point.toAlgHom x) a)
    have hx1 : Pl.subtype.comp xPl = rh 𝒢 x := RingHom.ext fun _ => rfl
    have hx2 : xPl.comp (algebraMap Rh (𝒢.level v)) = rPl hRA := by
      refine RingHom.ext fun r => Subtype.val_injective ?_
      exact DFunLike.congr_fun (rh_comp_algebraMap 𝒢 x) r
    refine ⟨⟨Spec.map (CommRingCat.ofHom xPl) ≫ ι v, ?_⟩, ?_⟩
    · rw [Category.assoc, hιbase, ← Category.assoc, specMap_ofHom_comp, hx2, σA_eq (Λ := Λ) hRA ρh hρh]
    · rw [pts_δ_coe, ← Category.assoc, barPt_comp_specMap, hx1]

include hRA hRloc hιp hιfin in

theorem exists_δ_eq_of_mem_finPts (v : ℕ) (y : JH M H) (hy : y ∈ O.finPts (p ^ v)) :
    ∃ x : 𝒢.Point ℚ̄ v, δ O 𝒢 ρh ι hρh hιbase v x = y := by
  have crit := ModularCurve.JHNeronObjectAtP.mem_finPts_iff_and_isTorsionPoint_section_and_specialPt p M H hpM Pl hPl Λ O (p ^ v)
  obtain ⟨-, s, hs⟩ := (crit.1 y).1 hy
  have htor : O.L.IsTorsionPoint Λ.σA (p ^ v) s := crit.2.2.1 y hy s hs
  have h3s : s.1 ≫ O.L.schemeNsmul (p ^ v) = (s.1 ≫ O.g) ≫ (O.L.one (𝟙 _)).1 :=
    coe_comp_schemeNsmul_of_isTorsionPoint O.L Λ.σA (p ^ v) s htor

  let sK : Spec (CommRingCat.of ↥Pl) ⟶
      pullback (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) :=
    pullback.lift s.1 (s.1 ≫ O.g) h3s
  have h4s : sK ≫ (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
      Spec.map (CommRingCat.ofHom (rPl hRA)) ≫ Spec.map (CommRingCat.ofHom ρh) := by
    rw [← Category.assoc, pullback.lift_fst, s.2, σA_eq (Λ := Λ) hRA ρh hρh]
  let xK := pullback.lift (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
    (g := Spec.map (CommRingCat.ofHom ρh)) sK (Spec.map (CommRingCat.ofHom (rPl hRA))) h4s
  haveI : IsLocalHom (CommRingCat.ofHom (rPl (Pl := Pl) hRA)).hom := isLocalHom_rPl hRA hRloc
  have hcl : (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
      (Spec.map (CommRingCat.ofHom ρh))).base (xK.base (IsLocalRing.closedPoint ↥Pl)) = IsLocalRing.closedPoint Rh := by
    change (xK ≫ pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
      (Spec.map (CommRingCat.ofHom ρh))).base (IsLocalRing.closedPoint ↥Pl) = _
    rw [pullback.lift_snd]
    exact Spec_closedPoint
  have h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
        (ι v) (ι v ≫ O.g) (hιp v) ≫
      (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
      Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh) := by
    rw [← Category.assoc, pullback.lift_fst]; exact hιbase v
  obtain ⟨hopen, -, hrange⟩ := hιfin v (hιp v) h4
  obtain ⟨τ, hτ⟩ := exists_comp_eq_of_isOpenImmersion_of_closedPoint_mem _ xK (hrange _ hcl)
  obtain ⟨ψ, hψ⟩ := exists_eq_specMap_ofHom (barPt Pl ≫ τ)
  have e1 := congrArg (· ≫ pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
      (Spec.map (CommRingCat.ofHom ρh))) hτ
  simp only [xK, sK, Category.assoc, pullback.lift_snd] at e1
  have e2 := congrArg (· ≫ pullback.fst (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
      (Spec.map (CommRingCat.ofHom ρh)) ≫ pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)) hτ
  simp only [xK, sK, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc] at e2
  have hψalg : ψ.comp (algebraMap Rh (𝒢.level v)) = algebraMap Rh ℚ̄ := by
    apply specMap_ofHom_inj
    rw [← specMap_ofHom_comp, ← hψ, Category.assoc, e1, barPt_comp_specMap, subtype_comp_rPl]
  let xa : 𝒢.level v →ₐ[Rh] ℚ̄ := ⟨ψ, fun r => DFunLike.congr_fun hψalg r⟩
  refine ⟨Point.ofAlgHom xa, eq_of_pts_coe_eq O ?_⟩
  rw [pts_δ_coe, hs]
  change Spec.map (CommRingCat.ofHom ψ) ≫ ι v = _
  rw [← hψ, Category.assoc, e2]

include hRA hRloc hιmul hιp hιfin in

theorem mem_finPts_iff (v : ℕ) (y : JH M H) :
    y ∈ O.finPts (p ^ v) ↔ ∃ x : 𝒢.Point ℚ̄ v, δ O 𝒢 ρh ι hρh hιbase v x = y :=
  ⟨exists_δ_eq_of_mem_finPts O hRA hRloc 𝒢 ρh ι hρh hιbase hιp hιfin v y, by
    rintro ⟨x, rfl⟩; exact δ_mem_finPts O hRA 𝒢 ρh ι hρh hιbase hιmul v x⟩

end Place
p2m_reactivate "P2MW.S_ModularCurve_exists_addMonoidHom_points_finitePart_eq_finPts_jHNeronObjectAtP_of_closedImmersion.TPts"

end TPts
p2m_reactivate "P2MW.S_ModularCurve_exists_addMonoidHom_points_finitePart_eq_finPts_jHNeronObjectAtP_of_closedImmersion.TPts"

set_option linter.unusedVariables false in
open ModularCurve in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    {h : ℕ}
    (𝒢 : PDivisibleGroup Rh p h)
    (ρh : ModularCurve.XHDRLevel.R p →+* Rh)
    (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
    (hρh : (algebraMap Rh (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hιcl : ∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h1))
    (hιp : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hιmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hιt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v)) ≫ ι (v + 1) = ι v)
    (hιfin : ∀ (v : ℕ)
      (h3 : ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρh))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρh))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρh))).base x = IsLocalRing.closedPoint Rh →
          x ∈ Set.range jv.base)

    :
    ∃ Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H,
      Function.Injective Δ ∧
      (∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y) ∧
      (∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z) ∧
      (∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.toricPts (p ^ v) →
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y) ∧
      (∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (O.pts (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] (AlgebraicClosure ℚ)) : 𝒢.level v →+* (AlgebraicClosure ℚ))) ≫ ι v) ∧

      (∀ (S : Set ℕ) (g : CohCarrier.Gen M S) (φ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v),
        (∀ v : ℕ, Spec.map (CommRingCat.ofHom (φ v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v = ι v ≫ (O.hecke S g).1) →
        ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) =
            ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))) := by

  classical
  refine ⟨TPts.Δ O 𝒢 ρh ι hρh hιbase hιmul hιt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact TPts.Δ_injective O 𝒢 ρh ι hρh hιbase hιmul hιt hιcl
  · intro v y
    rw [TPts.mem_finPts_iff O hRA hRloc 𝒢 ρh ι hρh hιbase hιmul hιp hιfin v y]
    simp only [TPts.Δ_mkAdd]
  · exact TPts.Δ_galois O 𝒢 ρh ι hρh hιbase hιmul hιt
  · intro v y hy
    obtain ⟨x, hx⟩ := TPts.exists_δ_eq_of_mem_finPts O hRA hRloc 𝒢 ρh ι hρh hιbase hιp hιfin v y
      (TPts.toricPts_le_finPts O _ hy)
    exact ⟨x, (TPts.Δ_mkAdd O 𝒢 ρh ι hρh hιbase hιmul hιt v x).trans hx⟩
  · intro v x
    rw [TPts.Δ_mkAdd, TPts.pts_δ_coe]
  · intro S g φ hφ v x
    exact TPts.Δ_hecke O 𝒢 ρh ι hρh hιbase hιmul hιt S g φ hφ v x

end S_ModularCurve_exists_addMonoidHom_points_finitePart_eq_finPts_jHNeronObjectAtP_of_closedImmersion
end P2MW
export P2MW.S_ModularCurve_exists_addMonoidHom_points_finitePart_eq_finPts_jHNeronObjectAtP_of_closedImmersion (solution)
