-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/946ceccc-4f84-51c9-bb43-1ee26e576b9e

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid.ModularCurve ModularCurve.JZeroNeronObjectAtP"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP"
namespace NeronCompare
namespace Tor
p2m_open "ModularCurve"

section fibre2

variable {R : Type} [CommRing R] {C : Scheme.{0}}
  {G G₀ : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)} {g₀ : G₀ ⟶ Spec (CommRingCat.of R)}

noncomputable def fibreRestrict₂ {ι ι₀ : C ⟶ Spec (CommRingCat.of R)} (hι : ι = ι₀) (Ψ : SchemeHomOver g g₀) :
    SchemeHomOver (pullback.snd g ι) (pullback.snd g₀ ι₀) :=
  ⟨pullback.lift (pullback.fst g ι ≫ Ψ.1) (pullback.snd g ι) (by rw [Category.assoc, Ψ.2, pullback.condition, hι]),
    pullback.lift_snd _ _ _⟩

@[scoped simp] theorem fibreRestrict₂_fst {ι ι₀ : C ⟶ Spec (CommRingCat.of R)} (hι : ι = ι₀) (Ψ : SchemeHomOver g g₀) :
    (fibreRestrict₂ hι Ψ).1 ≫ pullback.fst g₀ ι₀ = pullback.fst g ι ≫ Ψ.1 := by
  simp only [fibreRestrict₂, pullback.lift_fst]

@[scoped simp] theorem fibreRestrict₂_snd {ι ι₀ : C ⟶ Spec (CommRingCat.of R)} (hι : ι = ι₀) (Ψ : SchemeHomOver g g₀) :
    (fibreRestrict₂ hι Ψ).1 ≫ pullback.snd g₀ ι₀ = pullback.snd g ι := by
  simp only [fibreRestrict₂, pullback.lift_snd]

theorem fibreRestrict₂_rfl (ι : C ⟶ Spec (CommRingCat.of R)) (Ψ : SchemeHomOver g g₀) :
    fibreRestrict₂ (rfl : ι = ι) Ψ = fibreRestrictAlong ι g₀ g Ψ := rfl

end fibre2

section fibre2pts

variable {R R' : Type} [CommRing R] [CommRing R']
  {G G₀ : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)} {g₀ : G₀ ⟶ Spec (CommRingCat.of R)}

theorem toBase_comp_fibreRestrict₂ {ι ι₀ : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} (hι : ι = ι₀)
    (Ψ : SchemeHomOver g g₀) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R'))
    (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι g)) :
    RelativeGroupLaw.baseChangePointToBase ι₀ (NeronModelInfra.schemeHomOverComp x (fibreRestrict₂ hι Ψ)) =
      castOver (by rw [hι]) (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase ι x) Ψ) := by
  subst hι
  rw [fibreRestrict₂_rfl, RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong]
  rfl

theorem fibreRestrict₂_mul {ι ι₀ : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} (hι : ι = ι₀)
    (L : RelativeGroupLaw R g) (L₀ : RelativeGroupLaw R g₀) (Ψ : SchemeHomOver g g₀)
    {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R'))
    (hΨ : ∀ x y : SchemeHomOver (s ≫ ι) g, NeronModelInfra.schemeHomOverComp (L.mul _ x y) Ψ =
      L₀.mul _ (NeronModelInfra.schemeHomOverComp x Ψ) (NeronModelInfra.schemeHomOverComp y Ψ))
    (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι g)) :
    NeronModelInfra.schemeHomOverComp ((L.baseChange ι).mul s x y) (fibreRestrict₂ hι Ψ) =
      (L₀.baseChange ι₀).mul s (NeronModelInfra.schemeHomOverComp x (fibreRestrict₂ hι Ψ))
        (NeronModelInfra.schemeHomOverComp y (fibreRestrict₂ hι Ψ)) := by
  subst hι
  rw [fibreRestrict₂_rfl]
  apply (RelativeGroupLaw.baseChangePointEquiv ι s).injective
  change RelativeGroupLaw.baseChangePointToBase ι _ = RelativeGroupLaw.baseChangePointToBase ι _
  rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong, RelativeGroupLaw.baseChangePointToBase_mul,
    hΨ, RelativeGroupLaw.baseChangePointToBase_mul, RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong,
    RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong]

end fibre2pts

section laws

variable {R : Type} [CommRing R] {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}

theorem castOver_mul' (L : RelativeGroupLaw R g) {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s')
    (a b : SchemeHomOver s g) : castOver h (L.mul s a b) = L.mul s' (castOver h a) (castOver h b) := by
  subst h; rfl

theorem mul_eq_mul_of_eq (L Lc : RelativeGroupLaw R g) {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)}
    (h : s' = s) (hs : ∀ a b : SchemeHomOver s g, L.mul s a b = Lc.mul s a b) :
    ∀ a b : SchemeHomOver s' g, L.mul s' a b = Lc.mul s' a b := by
  subst h; exact hs

theorem eq_of_comp_eq {T T' : Scheme.{0}} [IsReduced T] [IsSeparated g] (s : T ⟶ Spec (CommRingCat.of R)) (j : T' ⟶ T) [IsDominant j]
    (a b : SchemeHomOver s g) (h : j ≫ a.1 = j ≫ b.1) : a = b := by
  apply Subtype.ext
  exact ext_of_isDominant_of_isSeparated g (by rw [a.2, b.2]) j h

theorem mul_eq_mul_of_dominant (L Lc : RelativeGroupLaw R g) {T T' : Scheme.{0}} [IsReduced T] [IsSeparated g]
    (s : T ⟶ Spec (CommRingCat.of R)) (j : T' ⟶ T) [IsDominant j]
    (hs : ∀ a b : SchemeHomOver (j ≫ s) g, L.mul _ a b = Lc.mul _ a b) :
    ∀ a b : SchemeHomOver s g, L.mul s a b = Lc.mul s a b := by
  intro a b
  apply eq_of_comp_eq s j
  have h := congrArg Subtype.val (hs (GoodReductionJacobian.schemeHomOverComp j rfl a) (GoodReductionJacobian.schemeHomOverComp j rfl b))
  rw [← L.mul_natural s (j ≫ s) j rfl, ← Lc.mul_natural s (j ≫ s) j rfl, GoodReductionJacobian.schemeHomOverComp_coe,
    GoodReductionJacobian.schemeHomOverComp_coe] at h
  exact h

theorem isDominant_barPt (A : ValuationSubring (AlgebraicClosure ℚ)) : IsDominant (barPt A) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap A.subtype)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective]
  exact bot_le

theorem mul_eq_mul_of_pts (L Lc : RelativeGroupLaw R g) {V : Type} [Add V] {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ _}
    (pts : V ≃ SchemeHomOver s g)
    (hL : ∀ v w : V, pts (v + w) = L.mul _ (pts v) (pts w)) (hLc : ∀ v w : V, pts (v + w) = Lc.mul _ (pts v) (pts w)) :
    ∀ a b : SchemeHomOver s g, L.mul s a b = Lc.mul s a b := by
  intro a b
  obtain ⟨v, rfl⟩ := pts.surjective a
  obtain ⟨w, rfl⟩ := pts.surjective b
  rw [← hL, hLc]

end laws

namespace KRect

abbrev red (t m : ℕ) : (Fin t → ℤ) →+ (Fin t → ZMod m) :=
  AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)

theorem red_apply (t m : ℕ) (z : Fin t → ℤ) (i : Fin t) : red t m z i = (z i : ZMod m) := rfl

private def _root_.ModularCurve.NeronCompare.Tor.KRect.lift (t m : ℕ) (g : Fin t → ZMod m) : Fin t → ℤ := fun i => ((g i).cast : ℤ)

p2m_export "ModularCurve.NeronCompare.Tor.KRect" "lift"
theorem red_lift (t m : ℕ) [NeZero m] (g : Fin t → ZMod m) : red t m (lift t m g) = g := by
  funext i
  simp [red_apply, lift, ZMod.intCast_zmod_cast]

theorem red_map_eq_of_red_eq (t t' m : ℕ) (M₀ : (Fin t' → ℤ) →+ (Fin t → ℤ)) (z z' : Fin t' → ℤ)
    (h : red t' m z = red t' m z') : red t m (M₀ z) = red t m (M₀ z') := by
  have hd : ∀ i, (m : ℤ) ∣ z i - z' i := by
    intro i
    have hi := congrFun h i
    rw [red_apply, red_apply] at hi
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub (z' i) (z i) m).mp hi.symm
  choose w hw using hd
  have hz : z = z' + (m : ℤ) • (fun i => w i) := by
    funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; have := hw i; omega
  funext i
  rw [red_apply, red_apply, hz, map_add, map_zsmul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add,
    Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]

def redHom (t t' m : ℕ) [NeZero m] (M₀ : (Fin t' → ℤ) →+ (Fin t → ℤ)) : (Fin t' → ZMod m) →+ (Fin t → ZMod m) where
  toFun g := red t m (M₀ (lift t' m g))
  map_zero' := by
    have h : red t' m (lift t' m 0) = red t' m 0 := by rw [red_lift, map_zero]
    rw [red_map_eq_of_red_eq t t' m M₀ _ _ h, map_zero, map_zero]
  map_add' g g' := by
    have h : red t' m (lift t' m (g + g')) = red t' m (lift t' m g + lift t' m g') := by
      rw [red_lift, map_add, red_lift, red_lift]
    rw [red_map_eq_of_red_eq t t' m M₀ _ _ h, map_add, map_add]

theorem redHom_red (t t' m : ℕ) [NeZero m] (M₀ : (Fin t' → ℤ) →+ (Fin t → ℤ)) (z : Fin t' → ℤ) :
    redHom t t' m M₀ (red t' m z) = red t m (M₀ z) := by
  show red t m (M₀ (lift t' m (red t' m z))) = red t m (M₀ z)
  apply red_map_eq_of_red_eq
  rw [red_lift]

theorem conv_single {S T : Type} [CommRing S] [CommRing T] [Algebra S T] {M : Type} [AddCommMonoid M]
    (χ ψ : WithConv (AddMonoidAlgebra S M →ₐ[S] T)) (g : M) :
    (χ * ψ).ofConv (AddMonoidAlgebra.single g 1) = χ.ofConv (AddMonoidAlgebra.single g 1) * ψ.ofConv (AddMonoidAlgebra.single g 1) := by
  rw [AlgHom.convMul_def]
  simp [AddMonoidAlgebra.comul_single, Algebra.TensorProduct.lmul'_apply_tmul]

theorem conv_comp_mapDomain {S T : Type} [CommRing S] [CommRing T] [Algebra S T] {M N : Type} [AddCommMonoid M] [AddCommMonoid N]
    (f : M →+ N) (χ ψ : WithConv (AddMonoidAlgebra S N →ₐ[S] T)) :
    (χ * ψ).ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S f) =
      (WithConv.toConv (χ.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S f)) *
        WithConv.toConv (ψ.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S f))).ofConv := by
  refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
  intro g
  rw [AlgHom.comp_apply, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single, conv_single, conv_single]
  simp only [WithConv.ofConv_toConv, AlgHom.comp_apply, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]

end KRect

section toricMatrix

open KRect

variable {p : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
  {G G₀ : Scheme.{0}} {g : G ⟶ base p} {g₀ : G₀ ⟶ base p}

theorem exists_redHom_forall_muPt_comp_eq
    (σ σ₀ : Spec (CommRingCat.of ↥A) ⟶ base p) (hσ : σ = σ₀)
    (L : RelativeGroupLaw (baseRing p) g) (L₀ : RelativeGroupLaw (baseRing p) g₀)
    (Ψ : SchemeHomOver g g₀) (Ψ' : SchemeHomOver g₀ g) (hΨΨ' : Ψ.1 ≫ Ψ'.1 = 𝟙 G) (hΨ'Ψ : Ψ'.1 ≫ Ψ.1 = 𝟙 G₀)
    (hΨ'mul : ∀ x y : SchemeHomOver (barPt A ≫ σ₀) g₀, NeronModelInfra.schemeHomOverComp (L₀.mul _ x y) Ψ' =
      L.mul _ (NeronModelInfra.schemeHomOverComp x Ψ') (NeronModelInfra.schemeHomOverComp y Ψ'))
    {t t₀ : ℕ} (m : ℕ) (hm : 0 < m)
    (ιm : SchemeHomOver (muStr ↥A t m) (RelativeGroupLaw.baseChangeStr σ g))
    (ι₀m : SchemeHomOver (muStr ↥A t₀ m) (RelativeGroupLaw.baseChangeStr σ₀ g₀))
    (hιm_mul : ∀ χ χ' : WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A t m (χ * χ').ofConv) ιm =
        (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A t m χ.ofConv) ιm)
          (NeronModelInfra.schemeHomOverComp (muPt A t m χ'.ofConv) ιm))
    (hι₀m_mul : ∀ χ χ' : WithConv (muCoord ↥A t₀ m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A t₀ m (χ * χ').ofConv) ι₀m =
        (L₀.baseChange σ₀).mul _ (NeronModelInfra.schemeHomOverComp (muPt A t₀ m χ.ofConv) ι₀m)
          (NeronModelInfra.schemeHomOverComp (muPt A t₀ m χ'.ofConv) ι₀m))
    (τ : SchemeHomOver (torusStr (ResidueField ↥A) t) (RelativeGroupLaw.baseChangeStr (resPt A ≫ σ) g))
    (τ₀ : SchemeHomOver (torusStr (ResidueField ↥A) t₀) (RelativeGroupLaw.baseChangeStr (resPt A ≫ σ₀) g₀))
    (hιm_sp : muBaseChange (residue ↥A) t m ≫ ιm.1 ≫ pullback.fst g σ =
      muToTorus (ResidueField ↥A) t m ≫ τ.1 ≫ pullback.fst g (resPt A ≫ σ))
    (hι₀m_sp : muBaseChange (residue ↥A) t₀ m ≫ ι₀m.1 ≫ pullback.fst g₀ σ₀ =
      muToTorus (ResidueField ↥A) t₀ m ≫ τ₀.1 ≫ pullback.fst g₀ (resPt A ≫ σ₀))
    (M₀ : (Fin t₀ → ℤ) →+ (Fin t → ℤ))
    (hM₀ : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫ τ₀.1 ≫
        pullback.fst g₀ (resPt A ≫ σ₀) = τ.1 ≫ pullback.fst g (resPt A ≫ σ) ≫ Ψ.1)
    (M₀' : (Fin t → ℤ) →+ (Fin t₀ → ℤ))
    (hM₀' : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀')) ≫ τ.1 ≫
        pullback.fst g (resPt A ≫ σ) = τ₀.1 ≫ pullback.fst g₀ (resPt A ≫ σ₀) ≫ Ψ'.1)
    (RIGID : ∀ u v : SchemeHomOver (muStr ↥A t m) (RelativeGroupLaw.baseChangeStr σ g),
      (∀ χ χ' : WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ),
        NeronModelInfra.schemeHomOverComp (muPt A t m (χ * χ').ofConv) u =
          (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A t m χ.ofConv) u)
            (NeronModelInfra.schemeHomOverComp (muPt A t m χ'.ofConv) u)) →
      (∀ χ χ' : WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ),
        NeronModelInfra.schemeHomOverComp (muPt A t m (χ * χ').ofConv) v =
          (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A t m χ.ofConv) v)
            (NeronModelInfra.schemeHomOverComp (muPt A t m χ'.ofConv) v)) →
      muBaseChange (residue ↥A) t m ≫ u.1 = muBaseChange (residue ↥A) t m ≫ v.1 → u = v) :
    ∃ Mbar : (Fin t₀ → ZMod m) →+ (Fin t → ZMod m),
      Mbar.comp (red t₀ m) = (red t m).comp M₀ ∧
      ∀ χ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ,
        (muPt A t m χ).1 ≫ ιm.1 ≫ pullback.fst g σ ≫ Ψ.1 =
          (muPt A t₀ m (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar))).1 ≫ ι₀m.1 ≫ pullback.fst g₀ σ₀ := by
  subst hσ
  classical
  haveI : NeZero m := ⟨hm.ne'⟩
  set κ := ResidueField ↥A with hκ

  let Mb : (Fin t₀ → ZMod m) →+ (Fin t → ZMod m) := redHom t t₀ m M₀
  let ψ : muCoord ↥A t₀ m →ₐ[↥A] muCoord ↥A t m := AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mb

  let Ψ'A : SchemeHomOver (RelativeGroupLaw.baseChangeStr σ g₀) (RelativeGroupLaw.baseChangeStr σ g) :=
    fibreRestrictAlong σ g g₀ Ψ'
  have hA_fst : Ψ'A.1 ≫ pullback.fst g σ = pullback.fst g₀ σ ≫ Ψ'.1 := fibreRestrictAlong_coe_comp_fst σ g g₀ Ψ'
  have Ψ'A_mul : ∀ x y : SchemeHomOver (barPt A) (RelativeGroupLaw.baseChangeStr σ g₀),
      NeronModelInfra.schemeHomOverComp ((L₀.baseChange σ).mul _ x y) Ψ'A =
        (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp x Ψ'A) (NeronModelInfra.schemeHomOverComp y Ψ'A) :=
    fun x y ↦ by simpa only [fibreRestrict₂_rfl] using fibreRestrict₂_mul rfl L₀ L Ψ' (barPt A) hΨ'mul x y

  let v₀ : SchemeHomOver (muStr ↥A t m) (RelativeGroupLaw.baseChangeStr σ g₀) :=
    ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ι₀m.1, by
      rw [Category.assoc, ι₀m.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2; exact ψ.comp_algebraMap⟩
  let v : SchemeHomOver (muStr ↥A t m) (RelativeGroupLaw.baseChangeStr σ g) := NeronModelInfra.schemeHomOverComp v₀ Ψ'A
  have hv1 : v.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ι₀m.1 ≫ Ψ'A.1 := by
    show (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ι₀m.1) ≫ Ψ'A.1 = _; rw [Category.assoc]

  have hpt_v₀ : ∀ θ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ,
      NeronModelInfra.schemeHomOverComp (muPt A t m θ) v₀ =
        NeronModelInfra.schemeHomOverComp (muPt A t₀ m (θ.comp ψ)) ι₀m := by
    intro θ
    apply Subtype.ext
    show Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ι₀m.1 =
      Spec.map (CommRingCat.ofHom (θ.comp ψ).toRingHom) ≫ ι₀m.1
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hpt_v : ∀ θ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ,
      NeronModelInfra.schemeHomOverComp (muPt A t m θ) v =
        NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (muPt A t₀ m (θ.comp ψ)) ι₀m) Ψ'A := by
    intro θ
    rw [← hpt_v₀]
    exact Subtype.ext (Category.assoc _ _ _).symm

  have hv : ∀ χ χ' : WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A t m (χ * χ').ofConv) v =
        (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A t m χ.ofConv) v)
          (NeronModelInfra.schemeHomOverComp (muPt A t m χ'.ofConv) v) := by
    intro χ χ'
    rw [hpt_v, hpt_v, hpt_v, conv_comp_mapDomain, hι₀m_mul, Ψ'A_mul]

  have hI1 : muBaseChange (residue ↥A) t m ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) =
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ Mb)) ≫ muBaseChange (residue ↥A) t₀ m := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply AddMonoidAlgebra.ringHom_ext
    · intro b
      simp [ψ, AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomainAlgHom_apply,
        AddMonoidAlgebra.mapDomain_single]
    · intro g
      simp [ψ, AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomainAlgHom_apply,
        AddMonoidAlgebra.mapDomain_single]
  have hI2 : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ Mb)) ≫ muToTorus κ t₀ m =
      muToTorus κ t m ≫ Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ M₀)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply AddMonoidAlgebra.ringHom_ext
    · intro b
      simp [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
    · intro g
      simp only [RingHom.comp_apply, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
      congr 1
      exact redHom_red t t₀ m M₀ g

  have hI1' : ∀ {X : Scheme.{0}} (k : _ ⟶ X), muBaseChange (residue ↥A) t m ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ k =
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ Mb)) ≫ muBaseChange (residue ↥A) t₀ m ≫ k :=
    fun k ↦ by simpa only [Category.assoc] using congrArg (· ≫ k) hI1
  have hI2' : ∀ {X : Scheme.{0}} (k : _ ⟶ X),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ Mb)) ≫ muToTorus κ t₀ m ≫ k =
        muToTorus κ t m ≫ Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ M₀)) ≫ k :=
    fun k ↦ by simpa only [Category.assoc] using congrArg (· ≫ k) hI2
  have hι₀m_sp' : ∀ {X : Scheme.{0}} (k : _ ⟶ X), muBaseChange (residue ↥A) t₀ m ≫ ι₀m.1 ≫ pullback.fst g₀ σ ≫ k =
      muToTorus κ t₀ m ≫ τ₀.1 ≫ pullback.fst g₀ (resPt A ≫ σ) ≫ k :=
    fun k ↦ by simpa only [Category.assoc] using congrArg (· ≫ k) hι₀m_sp
  have hM₀_' : ∀ {X : Scheme.{0}} (k : _ ⟶ X),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ M₀)) ≫ τ₀.1 ≫ pullback.fst g₀ (resPt A ≫ σ) ≫ k =
        τ.1 ≫ pullback.fst g (resPt A ≫ σ) ≫ Ψ.1 ≫ k :=
    fun k ↦ by simpa only [Category.assoc] using congrArg (· ≫ k) hM₀
  have hA_fst' : ∀ {X : Scheme.{0}} (k : _ ⟶ X), Ψ'A.1 ≫ pullback.fst g σ ≫ k = pullback.fst g₀ σ ≫ Ψ'.1 ≫ k :=
    fun k ↦ by simpa only [Category.assoc] using congrArg (· ≫ k) hA_fst

  have hkey : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ M₀)) ≫
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ M₀')) ≫ τ.1 ≫ pullback.fst g (resPt A ≫ σ) =
        τ.1 ≫ pullback.fst g (resPt A ≫ σ) := by
    rw [hM₀', hM₀_']
    simp only [hΨΨ', Category.comp_id]
  have R1 : muBaseChange (residue ↥A) t m ≫ v.1 ≫ pullback.fst g σ =
      muToTorus κ t m ≫ τ.1 ≫ pullback.fst g (resPt A ≫ σ) := by
    rw [hv1]
    simp only [Category.assoc]
    rw [hA_fst, hI1', hι₀m_sp', ← hM₀', hI2', hkey]
  have huv : muBaseChange (residue ↥A) t m ≫ ιm.1 = muBaseChange (residue ↥A) t m ≫ v.1 := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hιm_sp, R1]
    · have h2 : ∀ w : SchemeHomOver (muStr ↥A t m) (RelativeGroupLaw.baseChangeStr σ g),
          muBaseChange (residue ↥A) t m ≫ w.1 ≫ pullback.snd g σ =
            muBaseChange (residue ↥A) t m ≫ muStr ↥A t m := by
        intro w; rw [show w.1 ≫ pullback.snd g σ = muStr ↥A t m from w.2]
      rw [Category.assoc, Category.assoc, h2 ιm, h2 v]

  have huv' : ιm = v := RIGID ιm v hιm_mul hv huv
  refine ⟨Mb, AddMonoidHom.ext fun z => redHom_red t t₀ m M₀ z, fun χ => ?_⟩
  have hχ := congrArg Subtype.val (hpt_v χ)
  rw [← huv'] at hχ
  simp only [NeronModelInfra.schemeHomOverComp_coe] at hχ

  rw [← Category.assoc (muPt A t m χ).1, hχ]
  simp only [Category.assoc]
  rw [hA_fst', hΨ'Ψ, Category.comp_id]

end toricMatrix

end ModularCurve.NeronCompare.Tor
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid.ModularCurve.NeronCompare P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid.ModularCurve.NeronCompare.Tor"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid.ModularCurve.NeronCompare"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid.ModularCurve"

open ModularCurve.NeronCompare.Tor in
theorem solution
    {p : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {G G₀ : Scheme.{0}} {g : G ⟶ base p} {g₀ : G₀ ⟶ base p}
    (σ σ₀ : Spec (CommRingCat.of ↥A) ⟶ base p) (hσ : σ = σ₀)
    (L : RelativeGroupLaw (baseRing p) g) (L₀ : RelativeGroupLaw (baseRing p) g₀)
    (Ψ : SchemeHomOver g g₀) (Ψ' : SchemeHomOver g₀ g) (hΨΨ' : Ψ.1 ≫ Ψ'.1 = 𝟙 G) (hΨ'Ψ : Ψ'.1 ≫ Ψ.1 = 𝟙 G₀)
    (hΨ'mul : ∀ x y : SchemeHomOver (barPt A ≫ σ₀) g₀, NeronModelInfra.schemeHomOverComp (L₀.mul _ x y) Ψ' =
      L.mul _ (NeronModelInfra.schemeHomOverComp x Ψ') (NeronModelInfra.schemeHomOverComp y Ψ'))
    {t t₀ : ℕ} (m : ℕ) (hm : 0 < m)
    (ιm : SchemeHomOver (muStr ↥A t m) (RelativeGroupLaw.baseChangeStr σ g))
    (ι₀m : SchemeHomOver (muStr ↥A t₀ m) (RelativeGroupLaw.baseChangeStr σ₀ g₀))
    (hιm_mul : ∀ χ χ' : WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A t m (χ * χ').ofConv) ιm =
        (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A t m χ.ofConv) ιm)
          (NeronModelInfra.schemeHomOverComp (muPt A t m χ'.ofConv) ιm))
    (hι₀m_mul : ∀ χ χ' : WithConv (muCoord ↥A t₀ m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A t₀ m (χ * χ').ofConv) ι₀m =
        (L₀.baseChange σ₀).mul _ (NeronModelInfra.schemeHomOverComp (muPt A t₀ m χ.ofConv) ι₀m)
          (NeronModelInfra.schemeHomOverComp (muPt A t₀ m χ'.ofConv) ι₀m))
    (τ : SchemeHomOver (torusStr (ResidueField ↥A) t) (RelativeGroupLaw.baseChangeStr (resPt A ≫ σ) g))
    (τ₀ : SchemeHomOver (torusStr (ResidueField ↥A) t₀) (RelativeGroupLaw.baseChangeStr (resPt A ≫ σ₀) g₀))
    (hιm_sp : muBaseChange (residue ↥A) t m ≫ ιm.1 ≫ pullback.fst g σ =
      muToTorus (ResidueField ↥A) t m ≫ τ.1 ≫ pullback.fst g (resPt A ≫ σ))
    (hι₀m_sp : muBaseChange (residue ↥A) t₀ m ≫ ι₀m.1 ≫ pullback.fst g₀ σ₀ =
      muToTorus (ResidueField ↥A) t₀ m ≫ τ₀.1 ≫ pullback.fst g₀ (resPt A ≫ σ₀))
    (M₀ : (Fin t₀ → ℤ) →+ (Fin t → ℤ))
    (hM₀ : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫ τ₀.1 ≫
        pullback.fst g₀ (resPt A ≫ σ₀) = τ.1 ≫ pullback.fst g (resPt A ≫ σ) ≫ Ψ.1)
    (M₀' : (Fin t → ℤ) →+ (Fin t₀ → ℤ))
    (hM₀' : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀')) ≫ τ.1 ≫
        pullback.fst g (resPt A ≫ σ) = τ₀.1 ≫ pullback.fst g₀ (resPt A ≫ σ₀) ≫ Ψ'.1)
    (RIGID : ∀ u v : SchemeHomOver (muStr ↥A t m) (RelativeGroupLaw.baseChangeStr σ g),
      (∀ χ χ' : WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ),
        NeronModelInfra.schemeHomOverComp (muPt A t m (χ * χ').ofConv) u =
          (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A t m χ.ofConv) u)
            (NeronModelInfra.schemeHomOverComp (muPt A t m χ'.ofConv) u)) →
      (∀ χ χ' : WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ),
        NeronModelInfra.schemeHomOverComp (muPt A t m (χ * χ').ofConv) v =
          (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A t m χ.ofConv) v)
            (NeronModelInfra.schemeHomOverComp (muPt A t m χ'.ofConv) v)) →
      muBaseChange (residue ↥A) t m ≫ u.1 = muBaseChange (residue ↥A) t m ≫ v.1 → u = v) :
    ∃ Mbar : (Fin t₀ → ZMod m) →+ (Fin t → ZMod m),
      Mbar.comp (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t₀ => ℤ) i)) =
        (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)).comp M₀ ∧
      ∀ χ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ,
        (muPt A t m χ).1 ≫ ιm.1 ≫ pullback.fst g σ ≫ Ψ.1 =
          (muPt A t₀ m (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar))).1 ≫ ι₀m.1 ≫ pullback.fst g₀ σ₀ := by
  exact exists_redHom_forall_muPt_comp_eq σ σ₀ hσ L L₀ Ψ Ψ' hΨΨ' hΨ'Ψ hΨ'mul m hm ιm ι₀m hιm_mul hι₀m_mul τ τ₀ hιm_sp hι₀m_sp
    M₀ hM₀ M₀' hM₀' RIGID

end S_ModularCurve_JZeroNeronObjectAtP_exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid (solution)
