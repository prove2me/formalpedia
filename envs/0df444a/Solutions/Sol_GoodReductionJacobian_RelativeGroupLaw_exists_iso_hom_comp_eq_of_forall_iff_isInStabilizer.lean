-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_iso_hom_comp_eq_of_forall_iff_isInStabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/8939cd51-4c16-597e-aeb0-9900b7bbf5e6

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_of_forall_iff_isInStabilizer

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u v

namespace StabW2

theorem locallyIsoOver_pullback {X T : Scheme.{u}} {q : X ⟶ T} {M M' : X.Modules} (m : X ⟶ X)
    (hm : m ≫ q = q) (h : Scheme.Modules.LocallyIsoOver q M M') :
    Scheme.Modules.LocallyIsoOver q ((Scheme.Modules.pullback m).obj M) ((Scheme.Modules.pullback m).obj M') := by
  intro τ
  obtain ⟨U, hτ, ⟨e⟩⟩ := h τ
  refine ⟨U, hτ, ⟨?_⟩⟩
  have hle : q ⁻¹ᵁ U ≤ m ⁻¹ᵁ (q ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, hm]
  have hm' : m.resLE (q ⁻¹ᵁ U) (q ⁻¹ᵁ U) hle ≫ (q ⁻¹ᵁ U).ι = (q ⁻¹ᵁ U).ι ≫ m :=
    Scheme.Hom.resLE_comp_ι _ _
  exact (Scheme.Modules.pullbackComp (q ⁻¹ᵁ U).ι m).app M ≪≫
    (Scheme.Modules.pullbackCongr hm'.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (m.resLE (q ⁻¹ᵁ U) (q ⁻¹ᵁ U) hle) (q ⁻¹ᵁ U).ι).app M).symm ≪≫
    (Scheme.Modules.pullback (m.resLE (q ⁻¹ᵁ U) (q ⁻¹ᵁ U) hle)).mapIso e ≪≫
    (Scheme.Modules.pullbackComp (m.resLE (q ⁻¹ᵁ U) (q ⁻¹ᵁ U) hle) (q ⁻¹ᵁ U).ι).app M' ≪≫
    (Scheme.Modules.pullbackCongr hm').app M' ≪≫
    ((Scheme.Modules.pullbackComp (q ⁻¹ᵁ U).ι m).app M').symm

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

noncomputable def shift {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    pullback f t ⟶ pullback f t :=
  pullback.lift (L.mulRight t x) (pullback.snd f t) (L.mulRight_over t x)

@[scoped simp] theorem shift_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    shift L t x ≫ pullback.fst f t = L.mulRight t x := pullback.lift_fst _ _ _

@[scoped simp] theorem shift_snd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    shift L t x ≫ pullback.snd f t = pullback.snd f t := pullback.lift_snd _ _ _

theorem shift_over {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    shift L t x ≫ (pullback.snd f t ≫ t) = pullback.snd f t ≫ t := by
  rw [← Category.assoc, shift_snd]

theorem mulRight_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    L.mulRight t (L.mul t x y) = shift L t x ≫ L.mulRight t y := by
  have hR : shift L t x ≫ L.mulRight t y =
      (schemeHomOverComp (shift L t x) (shift_over L t x)
        (L.mul (pullback.snd f t ≫ t) (L.fstPoint t) (L.sndPoint t y))).1 := rfl
  rw [hR, L.mul_natural]
  have h1 : schemeHomOverComp (shift L t x) (shift_over L t x) (L.fstPoint t) =
      L.mul (pullback.snd f t ≫ t) (L.fstPoint t) (L.sndPoint t x) :=
    Subtype.ext (shift_fst L t x)
  have h2 : schemeHomOverComp (shift L t x) (shift_over L t x) (L.sndPoint t y) = L.sndPoint t y :=
    Subtype.ext (by simp only [schemeHomOverComp_coe, RelativeGroupLaw.sndPoint_coe, ← Category.assoc, shift_snd])
  rw [h1, h2]
  have h3 : L.sndPoint t (L.mul t x y) = schemeHomOverComp (pullback.snd f t) rfl (L.mul t x y) := Subtype.ext rfl
  have h4 : schemeHomOverComp (pullback.snd f t) rfl x = L.sndPoint t x := Subtype.ext rfl
  have h5 : schemeHomOverComp (pullback.snd f t) rfl y = L.sndPoint t y := Subtype.ext rfl
  show (L.mul (pullback.snd f t ≫ t) (L.fstPoint t) (L.sndPoint t (L.mul t x y))).1 = _
  rw [h3, L.mul_natural, h4, h5, L.mul_assoc]

theorem isInStabilizer_mul' (𝓛 : A.Modules) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f) (hx : L.IsInStabilizer 𝓛 t x) (hy : L.IsInStabilizer 𝓛 t y) :
    L.IsInStabilizer 𝓛 t (L.mul t x y) := by
  unfold RelativeGroupLaw.IsInStabilizer at hx hy ⊢

  have e1 : (Scheme.Modules.pullback (L.mulRight t (L.mul t x y))).obj 𝓛 ≅
      (Scheme.Modules.pullback (shift L t x)).obj ((Scheme.Modules.pullback (L.mulRight t y)).obj 𝓛) :=
    (Scheme.Modules.pullbackCongr (mulRight_mul L t x y)).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp (shift L t x) (L.mulRight t y)).app 𝓛).symm

  have e2 : (Scheme.Modules.pullback (shift L t x)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) ≅
      (Scheme.Modules.pullback (L.mulRight t x)).obj 𝓛 :=
    (Scheme.Modules.pullbackComp (shift L t x) (pullback.fst f t)).app 𝓛 ≪≫
      (Scheme.Modules.pullbackCongr (shift_fst L t x)).app 𝓛
  exact (Scheme.Modules.LocallyIsoOver.of_iso _ e1).trans
    ((locallyIsoOver_pullback (shift L t x) (shift_snd L t x) hy).trans
      ((Scheme.Modules.LocallyIsoOver.of_iso _ e2).trans hx))

theorem isInStabilizer_inv' (𝓛 : A.Modules) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) (hx : L.IsInStabilizer 𝓛 t x) :
    L.IsInStabilizer 𝓛 t (L.inv t x) := by
  unfold RelativeGroupLaw.IsInStabilizer at hx ⊢

  have hcomp : shift L t (L.inv t x) ≫ L.mulRight t x = pullback.fst f t := by
    rw [← mulRight_mul, L.inv_mul_cancel, L.mulRight_one]

  have e1 : (Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛 ≅
      (Scheme.Modules.pullback (shift L t (L.inv t x))).obj ((Scheme.Modules.pullback (L.mulRight t x)).obj 𝓛) :=
    (Scheme.Modules.pullbackCongr hcomp.symm).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp (shift L t (L.inv t x)) (L.mulRight t x)).app 𝓛).symm

  have e2 : (Scheme.Modules.pullback (shift L t (L.inv t x))).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) ≅
      (Scheme.Modules.pullback (L.mulRight t (L.inv t x))).obj 𝓛 :=
    (Scheme.Modules.pullbackComp (shift L t (L.inv t x)) (pullback.fst f t)).app 𝓛 ≪≫
      (Scheme.Modules.pullbackCongr (shift_fst L t (L.inv t x))).app 𝓛
  exact ((Scheme.Modules.LocallyIsoOver.of_iso _ e1).trans
    ((locallyIsoOver_pullback (shift L t (L.inv t x)) (shift_snd L t (L.inv t x)) hx).trans
      (Scheme.Modules.LocallyIsoOver.of_iso _ e2))).symm

noncomputable def constOver {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) : SchemeHomOver t f :=
  schemeHomOverComp t (Category.comp_id t) c

@[scoped simp] theorem constOver_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) : (constOver t c).1 = t ≫ c.1 := rfl

theorem comp_translate {Y : Scheme.{u}} (g : Y ⟶ A) (s : Y ⟶ Spec (CommRingCat.of R)) (hg : g ≫ f = s)
    (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    g ≫ L.translate c = (L.mul s ⟨g, hg⟩ (constOver s c)).1 := by
  have hR : g ≫ L.translate c =
      (schemeHomOverComp g hg (L.mul f RelativeGroupLaw.idPoint
        ⟨f ≫ c.1, by rw [Category.assoc, c.2, Category.comp_id]⟩)).1 := rfl
  rw [hR, L.mul_natural]
  have h1 : schemeHomOverComp g hg (RelativeGroupLaw.idPoint : SchemeHomOver f f) = ⟨g, hg⟩ :=
    Subtype.ext (Category.comp_id _)
  have h2 : schemeHomOverComp g hg
      (⟨f ≫ c.1, by rw [Category.assoc, c.2, Category.comp_id]⟩ : SchemeHomOver f f) = constOver s c :=
    Subtype.ext (by simp only [schemeHomOverComp_coe, constOver_coe, ← Category.assoc, hg])
  rw [h1, h2]

theorem translate_comp_translate (c d : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    L.translate c ≫ L.translate d = L.translate (L.mul (𝟙 _) c d) := by
  have hψ : L.translate c ≫ f = f := L.translate_over c
  have hR : L.translate c ≫ L.translate d =
      (schemeHomOverComp (L.translate c) hψ
        (L.mul f RelativeGroupLaw.idPoint ⟨f ≫ d.1, by rw [Category.assoc, d.2, Category.comp_id]⟩)).1 := rfl
  rw [hR, L.mul_natural]
  have h1 : schemeHomOverComp (L.translate c) hψ (RelativeGroupLaw.idPoint : SchemeHomOver f f) =
      L.mul f RelativeGroupLaw.idPoint ⟨f ≫ c.1, by rw [Category.assoc, c.2, Category.comp_id]⟩ :=
    Subtype.ext (Category.comp_id _)
  have h2 : schemeHomOverComp (L.translate c) hψ
      (⟨f ≫ d.1, by rw [Category.assoc, d.2, Category.comp_id]⟩ : SchemeHomOver f f) =
      ⟨f ≫ d.1, by rw [Category.assoc, d.2, Category.comp_id]⟩ :=
    Subtype.ext (by simp only [schemeHomOverComp_coe, ← Category.assoc, hψ])
  rw [h1, h2, L.mul_assoc]
  have h3 : L.mul f (⟨f ≫ c.1, by rw [Category.assoc, c.2, Category.comp_id]⟩ : SchemeHomOver f f)
      ⟨f ≫ d.1, by rw [Category.assoc, d.2, Category.comp_id]⟩ =
      ⟨f ≫ (L.mul (𝟙 _) c d).1, by rw [Category.assoc, (L.mul (𝟙 _) c d).2, Category.comp_id]⟩ :=
    (L.mul_natural (𝟙 (Spec (CommRingCat.of R))) f f (Category.comp_id f) c d).symm
  rw [h3]
  rfl

theorem translate_mul_inv (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    L.translate c ≫ L.translate (L.inv (𝟙 _) c) = 𝟙 A := by
  rw [translate_comp_translate, L.mul_inv_cancel, L.translate_one]

theorem translate_inv_mul (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    L.translate (L.inv (𝟙 _) c) ≫ L.translate c = 𝟙 A := by
  rw [translate_comp_translate, L.inv_mul_cancel, L.translate_one]

theorem exists_restrict_translate {K : Scheme.{u}} (𝓛 : A.Modules) (ι : K ⟶ A)
    (hK : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      (∃ κ : T ⟶ K, κ ≫ ι = x.1) ↔ L.IsInStabilizer 𝓛 t x)
    (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) (hc : ∃ κ : Spec (CommRingCat.of R) ⟶ K, κ ≫ ι = c.1) :
    ∃ τ : K ⟶ K, τ ≫ ι = ι ≫ L.translate c := by
  obtain ⟨κc, hκc⟩ := hc

  have hι : L.IsInStabilizer 𝓛 (ι ≫ f) ⟨ι, rfl⟩ := (hK (ι ≫ f) ⟨ι, rfl⟩).1 ⟨𝟙 K, Category.id_comp ι⟩
  have hcK : L.IsInStabilizer 𝓛 (ι ≫ f) (constOver (ι ≫ f) c) :=
    (hK (ι ≫ f) (constOver (ι ≫ f) c)).1 ⟨(ι ≫ f) ≫ κc, by rw [Category.assoc, hκc]; rfl⟩
  obtain ⟨τ, hτ⟩ := (hK (ι ≫ f) _).2 (isInStabilizer_mul' L 𝓛 (ι ≫ f) ⟨ι, rfl⟩ (constOver (ι ≫ f) c) hι hcK)
  exact ⟨τ, by rw [hτ, comp_translate L ι (ι ≫ f) rfl c]⟩

end StabW2
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_of_forall_iff_isInStabilizer.StabW2"

open StabW2

theorem solution
    {R : Type u} [CommRing R] {A K : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (𝓛 : A.Modules) (ι : K ⟶ A) [Mono ι]
    (hK : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      (∃ κ : T ⟶ K, κ ≫ ι = x.1) ↔ L.IsInStabilizer 𝓛 t x)
    (y₁ y₂ : Spec (CommRingCat.of R) ⟶ K) (h₁ : y₁ ≫ ι ≫ f = 𝟙 _) (h₂ : y₂ ≫ ι ≫ f = 𝟙 _) :
    ∃ τ : K ≅ K, τ.hom ≫ ι ≫ f = ι ≫ f ∧ y₁ ≫ τ.hom = y₂ := by

  let p₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f := ⟨y₁ ≫ ι, by rw [Category.assoc, h₁]⟩
  let p₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f := ⟨y₂ ≫ ι, by rw [Category.assoc, h₂]⟩
  have hp₁ : L.IsInStabilizer 𝓛 _ p₁ := (hK _ p₁).1 ⟨y₁, rfl⟩
  have hp₂ : L.IsInStabilizer 𝓛 _ p₂ := (hK _ p₂).1 ⟨y₂, rfl⟩
  let c : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f := L.mul _ (L.inv _ p₁) p₂
  have hc : L.IsInStabilizer 𝓛 _ c := isInStabilizer_mul' L 𝓛 _ _ _ (isInStabilizer_inv' L 𝓛 _ _ hp₁) hp₂
  have hc' : L.IsInStabilizer 𝓛 _ (L.inv _ c) := isInStabilizer_inv' L 𝓛 _ _ hc
  obtain ⟨τ, hτ⟩ := exists_restrict_translate L 𝓛 ι hK c ((hK _ c).2 hc)
  obtain ⟨τ', hτ'⟩ := exists_restrict_translate L 𝓛 ι hK (L.inv _ c) ((hK _ _).2 hc')
  have hττ' : τ ≫ τ' = 𝟙 K := by
    rw [← cancel_mono ι, Category.assoc, hτ', ← Category.assoc, hτ, Category.assoc, translate_mul_inv,
      Category.comp_id, Category.id_comp]
  have hτ'τ : τ' ≫ τ = 𝟙 K := by
    rw [← cancel_mono ι, Category.assoc, hτ, ← Category.assoc, hτ', Category.assoc, translate_inv_mul,
      Category.comp_id, Category.id_comp]
  refine ⟨⟨τ, τ', hττ', hτ'τ⟩, ?_, ?_⟩
  · show τ ≫ ι ≫ f = ι ≫ f
    rw [← Category.assoc, hτ, Category.assoc, L.translate_over]
  · show y₁ ≫ τ = y₂
    rw [← cancel_mono ι, Category.assoc, hτ, ← Category.assoc,
      comp_translate L (y₁ ≫ ι) (𝟙 _) (by rw [Category.assoc, h₁]) c]
    show (L.mul (𝟙 _) p₁ (constOver (𝟙 _) c)).1 = p₂.1
    have hcc : constOver (𝟙 (Spec (CommRingCat.of R))) c = c := Subtype.ext (Category.id_comp _)
    rw [hcc, ← L.mul_assoc, L.mul_inv_cancel, L.one_mul]

end S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_of_forall_iff_isInStabilizer
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_of_forall_iff_isInStabilizer (solution)
