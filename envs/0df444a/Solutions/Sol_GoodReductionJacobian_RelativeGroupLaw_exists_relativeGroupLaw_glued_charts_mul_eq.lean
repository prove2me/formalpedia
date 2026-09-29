-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_glued_charts_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/b82b4c6e-ff8b-5f11-802d-7b465d9b401b

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_glued_charts_mul_eq

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_glued_charts_mul_eq.GoodReductionJacobian"

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "IsCommutative pointGroup mul_inv_cancel one_natural mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul"
namespace GlueLaw72558c4a
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Points

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
  {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

abbrev ptK {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) f) :
    SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f :=
  GoodReductionJacobian.schemeHomOverComp σ rfl x

abbrev ptR {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) : SchemeHomOver s f :=
  GoodReductionJacobian.schemeHomOverComp s (Category.comp_id s) x

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) =
      L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  symm
  apply inv_eq_of_mul_eq_one_left
  show L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x))
    (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = L.one t'
  rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]

end Points

section Charts

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {Φ : Type u} [AddCommGroup Φ]
  (y : Φ → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) f)
  (c : Φ → Φ → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
  {N : Scheme.{u}}
  (e : Φ → (G ⟶ N))
  (t : Φ → Φ → (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≅
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in

def chartMul (φ ψ : Φ) : pullback f f ⟶ G :=
  (L.mul (pullback.fst f f ≫ f)
    (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
    (ptR (pullback.fst f f ≫ f) (c φ ψ))).1

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in
@[scoped simp] theorem chartMul_comp_f (φ ψ : Φ) : chartMul L c φ ψ ≫ f = pullback.fst f f ≫ f :=
  (L.mul _ _ _).2

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in

theorem lift_comp_chartMul {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (φ ψ : Φ)
    (a b : SchemeHomOver s f) :
    pullback.lift a.1 b.1 (a.2.trans b.2.symm) ≫ chartMul L c φ ψ =
      (L.mul s (L.mul s a b) (ptR s (c φ ψ))).1 := by
  have h : pullback.lift a.1 b.1 (a.2.trans b.2.symm) ≫ (pullback.fst f f ≫ f) = s := by
    rw [pullback.lift_fst_assoc]; exact a.2
  change (GoodReductionJacobian.schemeHomOverComp (pullback.lift a.1 b.1 (a.2.trans b.2.symm)) h
    (L.mul _ (L.mul _ _ _) _)).1 = _
  rw [L.mul_natural, L.mul_natural]
  have e1 : GoodReductionJacobian.schemeHomOverComp (pullback.lift a.1 b.1 (a.2.trans b.2.symm)) h
      (⟨pullback.fst f f, rfl⟩ : SchemeHomOver (pullback.fst f f ≫ f) f) = a := Subtype.ext (pullback.lift_fst _ _ _)
  have e2 : GoodReductionJacobian.schemeHomOverComp (pullback.lift a.1 b.1 (a.2.trans b.2.symm)) h
      (⟨pullback.snd f f, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst f f ≫ f) f) = b :=
    Subtype.ext (pullback.lift_snd _ _ _)
  have e3 : GoodReductionJacobian.schemeHomOverComp (pullback.lift a.1 b.1 (a.2.trans b.2.symm)) h
      (ptR (pullback.fst f f ≫ f) (c φ ψ)) = ptR s (c φ ψ) := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc, pullback.lift_fst_assoc]
    rw [reassoc_of% a.2]
  rw [e1, e2, e3]

theorem comp_comp_snd_eq_ptK {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of K))
    (l : T ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hlσ : l ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) = σ)
    (hl : l ≫ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K))) = σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) f) :
    GoodReductionJacobian.schemeHomOverComp l hl
      (GoodReductionJacobian.schemeHomOverComp (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        rfl x) = ptK K σ x := by
  apply Subtype.ext
  simp only [GoodReductionJacobian.schemeHomOverComp_coe]
  rw [← Category.assoc, hlσ]

theorem pt_eq_mul_of_comp_chart_eq
    (ht : ∀ φ ψ, (t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      (L.mul (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))), pullback.condition⟩
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) rfl
            (L.mul _ (y φ) (L.inv _ (y ψ))))).1)
    (hpb : ∀ φ ψ, φ ≠ ψ →
      IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        ((t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (e φ) (e ψ))
    [∀ φ, IsOpenImmersion (e φ)]
    {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of K)) (χ χ' : Φ)
    (a a' : SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f)
    (h : a.1 ≫ e χ = a'.1 ≫ e χ') :
    a' = L.mul _ a (L.mul _ (ptK K σ (y χ)) (L.inv _ (ptK K σ (y χ')))) := by
  by_cases hχ : χ = χ'
  · subst hχ
    have haa : a = a' := Subtype.ext ((cancel_mono (e χ)).mp h)
    subst haa
    rw [L.mul_inv_cancel, L.mul_one]
  · have H := hpb χ χ' hχ
    have hex : ∃ l : T ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))),
        l ≫ pullback.fst f _ = a.1 ∧ l ≫ ((t χ χ').hom ≫ pullback.fst f _) = a'.1 :=
      ⟨H.lift a.1 a'.1 h, H.lift_fst _ _ _, H.lift_snd _ _ _⟩
    obtain ⟨l, hl1, hl2⟩ := hex
    haveI : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
      IsPreimmersion.of_isLocalization (nonZeroDivisors R)
    have hlσ : l ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) = σ := by
      rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap R K))), Category.assoc,
        ← pullback.condition, ← Category.assoc, hl1]
      exact a.2
    have hl : l ≫ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K))) = σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
      rw [← Category.assoc, hlσ]
    apply Subtype.ext
    rw [← hl2, ht χ χ']
    change (GoodReductionJacobian.schemeHomOverComp l hl (L.mul _ _ _)).1 = _
    have hla : GoodReductionJacobian.schemeHomOverComp l hl
        (⟨pullback.fst f _, pullback.condition⟩ : SchemeHomOver (pullback.snd f (Spec.map (CommRingCat.ofHom
          (algebraMap R K))) ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f) = a := Subtype.ext hl1
    simp only [L.mul_natural, inv_natural, comp_comp_snd_eq_ptK σ _ hlσ hl, hla]

theorem comp_chart_eq_of_pt_eq_mul
    (ht : ∀ φ ψ, (t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      (L.mul (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))), pullback.condition⟩
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) rfl
            (L.mul _ (y φ) (L.inv _ (y ψ))))).1)
    (hpb : ∀ φ ψ, φ ≠ ψ →
      IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        ((t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (e φ) (e ψ))
    {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of K)) (χ χ' : Φ)
    (a a' : SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f)
    (h : a' = L.mul _ a (L.mul _ (ptK K σ (y χ)) (L.inv _ (ptK K σ (y χ'))))) :
    a.1 ≫ e χ = a'.1 ≫ e χ' := by
  by_cases hχ : χ = χ'
  · subst hχ
    rw [L.mul_inv_cancel, L.mul_one] at h
    subst h
    rfl
  · let l : T ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) := pullback.lift a.1 σ a.2
    have hlσ : l ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) = σ := pullback.lift_snd _ _ _
    have hl : l ≫ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K))) = σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
      rw [← Category.assoc, hlσ]
    have ha' : a'.1 = l ≫ (t χ χ').hom ≫ pullback.fst f _ := by
      rw [ht χ χ', h]
      change _ = (GoodReductionJacobian.schemeHomOverComp l hl (L.mul _ _ _)).1
      have hla : GoodReductionJacobian.schemeHomOverComp l hl
          (⟨pullback.fst f _, pullback.condition⟩ : SchemeHomOver (pullback.snd f (Spec.map (CommRingCat.ofHom
            (algebraMap R K))) ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f) = a :=
        Subtype.ext (pullback.lift_fst _ _ _)
      simp only [L.mul_natural, inv_natural, comp_comp_snd_eq_ptK σ _ hlσ hl, hla]
    calc a.1 ≫ e χ = l ≫ pullback.fst f _ ≫ e χ := by rw [pullback.lift_fst_assoc]
      _ = l ≫ ((t χ χ').hom ≫ pullback.fst f _) ≫ e χ' := by rw [(hpb χ χ' hχ).w]
      _ = a'.1 ≫ e χ' := by rw [ha']; simp only [Category.assoc]

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem ptR_c_eq
    (hc : ∀ φ ψ, Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ (c φ ψ).1 =
      (L.mul _ (L.mul _ (y φ) (y ψ)) (L.inv _ (y (φ + ψ)))).1)
    {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of K)) (φ ψ : Φ) :
    ptR (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) (c φ ψ) =
      L.mul _ (L.mul _ (ptK K σ (y φ)) (ptK K σ (y ψ))) (L.inv _ (ptK K σ (y (φ + ψ)))) := by
  apply Subtype.ext
  change (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ (c φ ψ).1 = _
  rw [Category.assoc, hc φ ψ]
  change (GoodReductionJacobian.schemeHomOverComp σ rfl
    (L.mul _ (L.mul _ (y φ) (y ψ)) (L.inv _ (y (φ + ψ))))).1 = _
  rw [L.mul_natural, L.mul_natural, inv_natural]

theorem chartMul_comp_chart_eq_of_generic (hL : L.IsCommutative)
    (hc : ∀ φ ψ, Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ (c φ ψ).1 =
      (L.mul _ (L.mul _ (y φ) (y ψ)) (L.inv _ (y (φ + ψ)))).1)
    (ht : ∀ φ ψ, (t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      (L.mul (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))), pullback.condition⟩
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) rfl
            (L.mul _ (y φ) (L.inv _ (y ψ))))).1)
    (hpb : ∀ φ ψ, φ ≠ ψ →
      IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        ((t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (e φ) (e ψ))
    [∀ φ, IsOpenImmersion (e φ)]
    {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of K)) (φ ψ φ' ψ' : Φ)
    (a b a' b' : SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f)
    (ha : a.1 ≫ e φ = a'.1 ≫ e φ') (hb : b.1 ≫ e ψ = b'.1 ≫ e ψ') :
    (L.mul _ (L.mul _ a b) (ptR _ (c φ ψ))).1 ≫ e (φ + ψ) =
      (L.mul _ (L.mul _ a' b') (ptR _ (c φ' ψ'))).1 ≫ e (φ' + ψ') := by
  have ha' := pt_eq_mul_of_comp_chart_eq L y e t ht hpb σ φ φ' a a' ha
  have hb' := pt_eq_mul_of_comp_chart_eq L y e t ht hpb σ ψ ψ' b b' hb
  apply comp_chart_eq_of_pt_eq_mul L y e t ht hpb σ (φ + ψ) (φ' + ψ')
  rw [ptR_c_eq L y c hc, ptR_c_eq L y c hc, ha', hb']
  letI : CommGroup (SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f) :=
    { L.pointGroup _ with mul_comm := hL _ }
  have hmul : ∀ u v : SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f,
      L.mul _ u v = u * v := fun _ _ => rfl
  have hinv : ∀ u : SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f,
      L.inv _ u = u⁻¹ := fun _ => rfl
  simp only [hmul, hinv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

variable (gN : N ⟶ Spec (CommRingCat.of R)) (hef : ∀ φ, e φ ≫ gN = f)

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in

def prodChart (φ ψ : Φ) : pullback f f ⟶ pullback gN gN :=
  pullback.map f f gN gN (e φ) (e ψ) (𝟙 _) (by rw [Category.comp_id, hef]) (by rw [Category.comp_id, hef])

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in
@[reassoc]
theorem prodChart_fst (φ ψ : Φ) : prodChart e gN hef φ ψ ≫ pullback.fst gN gN = pullback.fst f f ≫ e φ :=
  pullback.lift_fst _ _ _

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in
@[reassoc]
theorem prodChart_snd (φ ψ : Φ) : prodChart e gN hef φ ψ ≫ pullback.snd gN gN = pullback.snd f f ≫ e ψ :=
  pullback.lift_snd _ _ _

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in
theorem prodChart_fst_gN (φ ψ : Φ) :
    prodChart e gN hef φ ψ ≫ pullback.fst gN gN ≫ gN = pullback.fst f f ≫ f := by
  rw [prodChart_fst_assoc, hef]

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem lift_comp_eq_of_chart_sq (m : pullback gN gN ⟶ N)
    (hm : ∀ φ ψ : Φ, prodChart e gN hef φ ψ ≫ m = chartMul L c φ ψ ≫ e (φ + ψ))
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (φ ψ : Φ) (a b : SchemeHomOver s f) :
    pullback.lift (a.1 ≫ e φ) (b.1 ≫ e ψ) (by rw [Category.assoc, Category.assoc, hef, hef, a.2, b.2]) ≫ m =
      (L.mul s (L.mul s a b) (ptR s (c φ ψ))).1 ≫ e (φ + ψ) := by
  have h : pullback.lift (a.1 ≫ e φ) (b.1 ≫ e ψ) (by rw [Category.assoc, Category.assoc, hef, hef, a.2, b.2]) =
      pullback.lift a.1 b.1 (a.2.trans b.2.symm) ≫ prodChart e gN hef φ ψ := by
    apply pullback.hom_ext <;> simp [prodChart_fst, prodChart_snd]
  rw [h, Category.assoc, hm, ← Category.assoc, lift_comp_chartMul]

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in

def chartCover [∀ φ, IsOpenImmersion (e φ)] (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ) : N.OpenCover :=
  Scheme.Cover.mkOfCovers Φ (fun _ => G) e (fun x => by
    have hx : x ∈ ⋃ φ, Set.range (e φ).base := by rw [hecov]; trivial
    obtain ⟨φ, z, hz⟩ := Set.mem_iUnion.mp hx
    exact ⟨φ, z, hz⟩)

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in

def prodChartCover [∀ φ, IsOpenImmersion (e φ)] (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ) :
    (pullback gN gN).OpenCover :=
  (Scheme.Pullback.openCoverOfLeftRight (chartCover e hecov) (chartCover e hecov) gN gN).copy (Φ × Φ)
    (fun _ => pullback f f) (fun i => prodChart e gN hef i.1 i.2) (Equiv.refl _)
    (fun i => pullback.congrHom (hef i.1).symm (hef i.2).symm)
    (fun i => by
      apply pullback.hom_ext <;>
        simp [prodChart, chartCover, Scheme.Pullback.openCoverOfLeftRight_f, pullback.congrHom_hom,
          Scheme.Cover.mkOfCovers, pullback.map] <;>
        (first | erw [pullback.lift_fst_assoc] | erw [pullback.lift_snd_assoc]) <;> rfl)

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in
theorem prodChartCover_f [∀ φ, IsOpenImmersion (e φ)] (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ)
    (i : Φ × Φ) : (prodChartCover e gN hef hecov).f i = prodChart e gN hef i.1 i.2 := rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in
theorem isOpenImmersion_prodChart [∀ φ, IsOpenImmersion (e φ)]
    (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ) (φ ψ : Φ) : IsOpenImmersion (prodChart e gN hef φ ψ) :=
  (prodChartCover e gN hef hecov).map_prop (φ, ψ)

theorem overlap_compat (hL : L.IsCommutative) [Flat f] [IsSeparated gN]
    (hc : ∀ φ ψ, Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ (c φ ψ).1 =
      (L.mul _ (L.mul _ (y φ) (y ψ)) (L.inv _ (y (φ + ψ)))).1)
    (ht : ∀ φ ψ, (t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      (L.mul (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))), pullback.condition⟩
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) rfl
            (L.mul _ (y φ) (L.inv _ (y ψ))))).1)
    (hpb : ∀ φ ψ, φ ≠ ψ →
      IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        ((t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (e φ) (e ψ))
    [∀ φ, IsOpenImmersion (e φ)] (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ) (φ ψ φ' ψ' : Φ) :
    pullback.fst (prodChart e gN hef φ ψ) (prodChart e gN hef φ' ψ') ≫ chartMul L c φ ψ ≫ e (φ + ψ) =
      pullback.snd (prodChart e gN hef φ ψ) (prodChart e gN hef φ' ψ') ≫ chartMul L c φ' ψ' ≫ e (φ' + ψ') := by
  haveI := isOpenImmersion_prodChart e gN hef hecov φ' ψ'
  haveI := isOpenImmersion_prodChart e gN hef hecov φ ψ
  have hW : pullback.snd (prodChart e gN hef φ ψ) (prodChart e gN hef φ' ψ') ≫ pullback.fst f f ≫ f =
      pullback.fst (prodChart e gN hef φ ψ) (prodChart e gN hef φ' ψ') ≫ pullback.fst f f ≫ f := by
    have h := congrArg (· ≫ pullback.fst gN gN ≫ gN)
      (pullback.condition (f := prodChart e gN hef φ ψ) (g := prodChart e gN hef φ' ψ'))
    simp only [Category.assoc, prodChart_fst_gN] at h
    exact h.symm
  have hWfst : pullback.fst (prodChart e gN hef φ ψ) (prodChart e gN hef φ' ψ') ≫ pullback.fst f f ≫ e φ =
      pullback.snd (prodChart e gN hef φ ψ) (prodChart e gN hef φ' ψ') ≫ pullback.fst f f ≫ e φ' := by
    have h := congrArg (· ≫ pullback.fst gN gN)
      (pullback.condition (f := prodChart e gN hef φ ψ) (g := prodChart e gN hef φ' ψ'))
    simp only [Category.assoc, prodChart_fst] at h
    exact h
  have hWsnd : pullback.fst (prodChart e gN hef φ ψ) (prodChart e gN hef φ' ψ') ≫ pullback.snd f f ≫ e ψ =
      pullback.snd (prodChart e gN hef φ ψ) (prodChart e gN hef φ' ψ') ≫ pullback.snd f f ≫ e ψ' := by
    have h := congrArg (· ≫ pullback.snd gN gN)
      (pullback.condition (f := prodChart e gN hef φ ψ) (g := prodChart e gN hef φ' ψ'))
    simp only [Category.assoc, prodChart_snd] at h
    exact h
  haveI hflat : Flat (pullback.fst (prodChart e gN hef φ ψ) (prodChart e gN hef φ' ψ') ≫ pullback.fst f f ≫ f) :=
    inferInstance
  let u₁ : SchemeHomOver (pullback.fst (prodChart e gN hef φ ψ) (prodChart e gN hef φ' ψ') ≫ pullback.fst f f ≫ f) gN :=
    ⟨pullback.fst _ _ ≫ chartMul L c φ ψ ≫ e (φ + ψ), by simp only [Category.assoc, hef, chartMul_comp_f]⟩
  let u₂ : SchemeHomOver (pullback.fst (prodChart e gN hef φ ψ) (prodChart e gN hef φ' ψ') ≫ pullback.fst f f ≫ f) gN :=
    ⟨pullback.snd _ _ ≫ chartMul L c φ' ψ' ≫ e (φ' + ψ'), by simp only [Category.assoc, hef, chartMul_comp_f]; exact hW⟩
  suffices hu : genericFibreRestrict R K gN _ u₁ = genericFibreRestrict R K gN _ u₂ from
    congrArg Subtype.val (NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R K gN _ hu)
  apply Subtype.ext
  apply pullback.hom_ext
  swap
  · rw [genericFibreRestrict_coe_comp_snd, genericFibreRestrict_coe_comp_snd]
  rw [genericFibreRestrict_coe_comp_fst, genericFibreRestrict_coe_comp_fst]

  set p := pullback.fst (pullback.fst (prodChart e gN hef φ ψ) (prodChart e gN hef φ' ψ') ≫ pullback.fst f f ≫ f)
    (specGenericFibreInclusion R K) with hp_def
  set σ := pullback.snd (pullback.fst (prodChart e gN hef φ ψ) (prodChart e gN hef φ' ψ') ≫ pullback.fst f f ≫ f)
    (specGenericFibreInclusion R K) with hσ_def
  have hp : p ≫ pullback.fst (prodChart e gN hef φ ψ) (prodChart e gN hef φ' ψ') ≫ pullback.fst f f ≫ f =
      σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := pullback.condition
  let a : SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f :=
    ⟨(p ≫ pullback.fst _ _) ≫ pullback.fst f f, by simpa only [Category.assoc] using hp⟩
  let b : SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f :=
    ⟨(p ≫ pullback.fst _ _) ≫ pullback.snd f f, by
      rw [Category.assoc, ← pullback.condition]; simpa only [Category.assoc] using hp⟩
  let a' : SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f :=
    ⟨(p ≫ pullback.snd _ _) ≫ pullback.fst f f, by
      rw [Category.assoc, Category.assoc, hW]; simpa only [Category.assoc] using hp⟩
  let b' : SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f :=
    ⟨(p ≫ pullback.snd _ _) ≫ pullback.snd f f, by
      rw [Category.assoc, Category.assoc, ← pullback.condition, hW]; simpa only [Category.assoc] using hp⟩
  have hpa : pullback.lift a.1 b.1 (a.2.trans b.2.symm) = p ≫ pullback.fst _ _ := by
    apply pullback.hom_ext <;> simp [a, b]
  have hpa' : pullback.lift a'.1 b'.1 (a'.2.trans b'.2.symm) = p ≫ pullback.snd _ _ := by
    apply pullback.hom_ext <;> simp [a', b']
  have e1 := lift_comp_chartMul L c _ φ ψ a b
  have e2 := lift_comp_chartMul L c _ φ' ψ' a' b'
  rw [hpa, Category.assoc] at e1
  rw [hpa', Category.assoc] at e2
  show p ≫ pullback.fst _ _ ≫ chartMul L c φ ψ ≫ e (φ + ψ) = p ≫ pullback.snd _ _ ≫ chartMul L c φ' ψ' ≫ e (φ' + ψ')
  rw [reassoc_of% e1, reassoc_of% e2]
  apply chartMul_comp_chart_eq_of_generic L y c e t hL hc ht hpb σ φ ψ φ' ψ' a b a' b'
  · simp only [a, a', Category.assoc]; rw [hWfst]
  · simp only [b, b', Category.assoc]; rw [hWsnd]

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in
include hef in

theorem flat_gN [Flat f] [∀ φ, IsOpenImmersion (e φ)] (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ) :
    Flat gN :=
  IsZariskiLocalAtSource.of_openCover (P := @Flat) (chartCover e hecov) (fun φ => by
    change Flat (e φ ≫ gN); rw [hef]; infer_instance)

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in

def mulPt (m : pullback gN gN ⟶ N) (hmg : m ≫ gN = pullback.fst gN gN ≫ gN)
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver s gN) : SchemeHomOver s gN :=
  ⟨pullback.lift u.1 v.1 (u.2.trans v.2.symm) ≫ m, by rw [Category.assoc, hmg, pullback.lift_fst_assoc, u.2]⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in
@[scoped simp] theorem mulPt_coe (m : pullback gN gN ⟶ N) (hmg : m ≫ gN = pullback.fst gN gN ≫ gN)
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver s gN) :
    (mulPt gN m hmg s u v).1 = pullback.lift u.1 v.1 (u.2.trans v.2.symm) ≫ m := rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in
theorem mulPt_natural (m : pullback gN gN ⟶ N) (hmg : m ≫ gN = pullback.fst gN gN ≫ gN)
    {T T' : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (s' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ s = s') (u v : SchemeHomOver s gN) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (mulPt gN m hmg s u v) =
      mulPt gN m hmg s' (GoodReductionJacobian.schemeHomOverComp ψ hψ u)
        (GoodReductionJacobian.schemeHomOverComp ψ hψ v) := by
  apply Subtype.ext
  simp only [GoodReductionJacobian.schemeHomOverComp_coe, mulPt_coe, ← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem mulPt_chart (m : pullback gN gN ⟶ N) (hmg : m ≫ gN = pullback.fst gN gN ≫ gN)
    (hm : ∀ φ ψ : Φ, prodChart e gN hef φ ψ ≫ m = chartMul L c φ ψ ≫ e (φ + ψ))
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (φ ψ : Φ) (a b : SchemeHomOver s f) :
    mulPt gN m hmg s (NeronModelInfra.schemeHomOverComp a ⟨e φ, hef φ⟩)
        (NeronModelInfra.schemeHomOverComp b ⟨e ψ, hef ψ⟩) =
      NeronModelInfra.schemeHomOverComp (L.mul s (L.mul s a b) (ptR s (c φ ψ))) ⟨e (φ + ψ), hef (φ + ψ)⟩ := by
  apply Subtype.ext
  simp only [mulPt_coe, NeronModelInfra.schemeHomOverComp_coe]
  exact lift_comp_eq_of_chart_sq L c e gN hef m hm s φ ψ a b

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in

abbrev idPt : SchemeHomOver f f := ⟨𝟙 G, Category.id_comp f⟩

omit [IsDomain R] [IsDiscreteValuationRing R] in

def chartInvG (φ : Φ) : G ⟶ G :=
  (L.mul f (L.inv f idPt) (L.inv f (ptR f (c φ (-φ))))).1

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[scoped simp] theorem chartInvG_comp_f (φ : Φ) : chartInvG L c φ ≫ f = f :=
  (L.mul _ _ _).2

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem comp_chartInvG {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (φ : Φ) (a : SchemeHomOver s f) :
    a.1 ≫ chartInvG L c φ = (L.mul s (L.inv s a) (L.inv s (ptR s (c φ (-φ))))).1 := by
  change (GoodReductionJacobian.schemeHomOverComp a.1 a.2 (L.mul f (L.inv f idPt) (L.inv f (ptR f (c φ (-φ)))))).1 = _
  rw [L.mul_natural, inv_natural, inv_natural]
  have e1 : GoodReductionJacobian.schemeHomOverComp a.1 a.2 (idPt : SchemeHomOver f f) = a :=
    Subtype.ext (Category.comp_id _)
  have e2 : GoodReductionJacobian.schemeHomOverComp a.1 a.2 (ptR f (c φ (-φ))) = ptR s (c φ (-φ)) := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe]
    rw [reassoc_of% a.2]
  rw [e1, e2]

include hef in

theorem overlap_compat_inv (hL : L.IsCommutative) [Flat f] [IsSeparated gN]
    (hc : ∀ φ ψ, Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ (c φ ψ).1 =
      (L.mul _ (L.mul _ (y φ) (y ψ)) (L.inv _ (y (φ + ψ)))).1)
    (ht : ∀ φ ψ, (t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      (L.mul (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))), pullback.condition⟩
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) rfl
            (L.mul _ (y φ) (L.inv _ (y ψ))))).1)
    (hpb : ∀ φ ψ, φ ≠ ψ →
      IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        ((t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (e φ) (e ψ))
    [∀ φ, IsOpenImmersion (e φ)] (φ φ' : Φ) :
    pullback.fst (e φ) (e φ') ≫ chartInvG L c φ ≫ e (-φ) =
      pullback.snd (e φ) (e φ') ≫ chartInvG L c φ' ≫ e (-φ') := by
  haveI hflat : Flat (pullback.fst (e φ) (e φ') ≫ f) := inferInstance
  have hW : pullback.snd (e φ) (e φ') ≫ f = pullback.fst (e φ) (e φ') ≫ f := by
    have h := congrArg (· ≫ gN) (pullback.condition (f := e φ) (g := e φ'))
    simp only [Category.assoc, hef] at h
    exact h.symm
  let u₁ : SchemeHomOver (pullback.fst (e φ) (e φ') ≫ f) gN :=
    ⟨pullback.fst _ _ ≫ chartInvG L c φ ≫ e (-φ), by simp only [Category.assoc, hef, chartInvG_comp_f]⟩
  let u₂ : SchemeHomOver (pullback.fst (e φ) (e φ') ≫ f) gN :=
    ⟨pullback.snd _ _ ≫ chartInvG L c φ' ≫ e (-φ'), by simp only [Category.assoc, hef, chartInvG_comp_f]; exact hW⟩
  suffices hu : genericFibreRestrict R K gN _ u₁ = genericFibreRestrict R K gN _ u₂ from
    congrArg Subtype.val (NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R K gN _ hu)
  apply Subtype.ext
  apply pullback.hom_ext
  swap
  · rw [genericFibreRestrict_coe_comp_snd, genericFibreRestrict_coe_comp_snd]
  rw [genericFibreRestrict_coe_comp_fst, genericFibreRestrict_coe_comp_fst]
  set p := pullback.fst (pullback.fst (e φ) (e φ') ≫ f) (specGenericFibreInclusion R K) with hp_def
  set σ := pullback.snd (pullback.fst (e φ) (e φ') ≫ f) (specGenericFibreInclusion R K) with hσ_def
  have hp : p ≫ pullback.fst (e φ) (e φ') ≫ f = σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) :=
    pullback.condition
  let a : SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f :=
    ⟨p ≫ pullback.fst _ _, by simpa only [Category.assoc] using hp⟩
  let a' : SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f :=
    ⟨p ≫ pullback.snd _ _, by rw [Category.assoc, hW]; exact hp⟩
  show p ≫ pullback.fst _ _ ≫ chartInvG L c φ ≫ e (-φ) = p ≫ pullback.snd _ _ ≫ chartInvG L c φ' ≫ e (-φ')
  rw [← Category.assoc p, ← Category.assoc p, ← Category.assoc (p ≫ _), ← Category.assoc (p ≫ _),
    comp_chartInvG L c _ φ a, comp_chartInvG L c _ φ' a']
  have ha' := pt_eq_mul_of_comp_chart_eq L y e t ht hpb σ φ φ' a a' (by
    simp only [a, a', Category.assoc]; rw [pullback.condition])
  apply comp_chart_eq_of_pt_eq_mul L y e t ht hpb σ (-φ) (-φ')
  rw [ptR_c_eq L y c hc, ptR_c_eq L y c hc, ha']
  letI : CommGroup (SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f) :=
    { L.pointGroup _ with mul_comm := hL _ }
  have hmul : ∀ u v : SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f,
      L.mul _ u v = u * v := fun _ _ => rfl
  have hinv : ∀ u : SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f,
      L.inv _ u = u⁻¹ := fun _ => rfl
  simp only [hmul, hinv, neg_add_cancel, add_neg_cancel]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

include hef in

theorem glueLaw_exists_inv (hL : L.IsCommutative) [Flat f] [IsSeparated gN]
    (hc : ∀ φ ψ, Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ (c φ ψ).1 =
      (L.mul _ (L.mul _ (y φ) (y ψ)) (L.inv _ (y (φ + ψ)))).1)
    (ht : ∀ φ ψ, (t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      (L.mul (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))), pullback.condition⟩
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) rfl
            (L.mul _ (y φ) (L.inv _ (y ψ))))).1)
    (hpb : ∀ φ ψ, φ ≠ ψ →
      IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        ((t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (e φ) (e ψ))
    [∀ φ, IsOpenImmersion (e φ)] (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ) :
    ∃ ιN : N ⟶ N, ιN ≫ gN = gN ∧ ∀ φ : Φ, e φ ≫ ιN = chartInvG L c φ ≫ e (-φ) := by
  refine ⟨(chartCover e hecov).glueMorphisms (fun φ : Φ => chartInvG L c φ ≫ e (-φ)) (fun (φ : Φ) (φ' : Φ) => ?_),
    ?_, fun φ => ?_⟩
  · exact overlap_compat_inv L y c e t gN hef hL hc ht hpb φ φ'
  · apply Scheme.Cover.hom_ext (chartCover e hecov)
    rintro (φ : Φ)
    rw [Scheme.Cover.ι_glueMorphisms_assoc]
    change (chartInvG L c φ ≫ e (-φ)) ≫ gN = e φ ≫ gN
    rw [Category.assoc, hef, hef, chartInvG_comp_f]
  · exact (chartCover e hecov).ι_glueMorphisms _ _ φ

omit [IsDomain R] [IsDiscreteValuationRing R] in

def onePt {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) : SchemeHomOver s gN :=
  NeronModelInfra.schemeHomOverComp (L.one s) ⟨e 0, hef 0⟩

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem onePt_natural {T T' : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (s' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ s = s') :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (onePt L e gN hef s) = onePt L e gN hef s' := by
  apply Subtype.ext
  have h := congrArg Subtype.val (L.one_natural s s' ψ hψ)
  simp only [GoodReductionJacobian.schemeHomOverComp_coe] at h
  simp only [onePt, GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe,
    ← Category.assoc, h]

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in

def invPt (ιN : N ⟶ N) (hιg : ιN ≫ gN = gN) {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R))
    (u : SchemeHomOver s gN) : SchemeHomOver s gN :=
  ⟨u.1 ≫ ιN, by rw [Category.assoc, hιg, u.2]⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in
@[scoped simp] theorem invPt_coe (ιN : N ⟶ N) (hιg : ιN ≫ gN = gN) {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R))
    (u : SchemeHomOver s gN) : (invPt gN ιN hιg s u).1 = u.1 ≫ ιN := rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup Φ] in
theorem invPt_natural (ιN : N ⟶ N) (hιg : ιN ≫ gN = gN)
    {T T' : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (s' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ s = s') (u : SchemeHomOver s gN) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (invPt gN ιN hιg s u) =
      invPt gN ιN hιg s' (GoodReductionJacobian.schemeHomOverComp ψ hψ u) :=
  Subtype.ext (Category.assoc _ _ _).symm

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem invPt_chart (ιN : N ⟶ N) (hιg : ιN ≫ gN = gN) (hι : ∀ φ : Φ, e φ ≫ ιN = chartInvG L c φ ≫ e (-φ))
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (φ : Φ) (a : SchemeHomOver s f) :
    invPt gN ιN hιg s (NeronModelInfra.schemeHomOverComp a ⟨e φ, hef φ⟩) =
      NeronModelInfra.schemeHomOverComp (L.mul s (L.inv s a) (L.inv s (ptR s (c φ (-φ))))) ⟨e (-φ), hef (-φ)⟩ := by
  apply Subtype.ext
  simp only [invPt_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc, hι]
  rw [← Category.assoc, comp_chartInvG]

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem ptR_c00 (hc0 : c 0 0 = L.one _) {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) :
    ptR s (c 0 0) = L.one s := by
  rw [hc0]; exact L.one_natural _ _ _ _

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem mulPt_chart0 (hc0 : c 0 0 = L.one _) (m : pullback gN gN ⟶ N) (hmg : m ≫ gN = pullback.fst gN gN ≫ gN)
    (hm : ∀ φ ψ : Φ, prodChart e gN hef φ ψ ≫ m = chartMul L c φ ψ ≫ e (φ + ψ))
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver s f) :
    mulPt gN m hmg s (NeronModelInfra.schemeHomOverComp a ⟨e 0, hef 0⟩)
        (NeronModelInfra.schemeHomOverComp b ⟨e 0, hef 0⟩) =
      NeronModelInfra.schemeHomOverComp (L.mul s a b) ⟨e 0, hef 0⟩ := by
  apply Subtype.ext
  simp only [mulPt_coe, NeronModelInfra.schemeHomOverComp_coe]
  rw [lift_comp_eq_of_chart_sq L c e gN hef m hm s 0 0 a b, add_zero, ptR_c00 L c hc0, L.mul_one]

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem invPt_chart0 (hc0 : c 0 0 = L.one _) (ιN : N ⟶ N) (hιg : ιN ≫ gN = gN)
    (hι : ∀ φ : Φ, e φ ≫ ιN = chartInvG L c φ ≫ e (-φ))
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver s f) :
    invPt gN ιN hιg s (NeronModelInfra.schemeHomOverComp a ⟨e 0, hef 0⟩) =
      NeronModelInfra.schemeHomOverComp (L.inv s a) ⟨e 0, hef 0⟩ := by
  apply Subtype.ext
  rw [congrArg Subtype.val (invPt_chart L c e gN hef ιN hιg hι s 0 a)]
  simp only [NeronModelInfra.schemeHomOverComp_coe]
  rw [neg_zero, ptR_c00 L c hc0]
  letI := L.pointGroup s
  change ((a⁻¹ * (1 : SchemeHomOver s f)⁻¹ : SchemeHomOver s f)).1 ≫ e 0 = (a⁻¹ : SchemeHomOver s f).1 ≫ e 0
  rw [inv_one, _root_.mul_one]

include hef in

theorem exists_pt_eq_comp_chart
    (hpb : ∀ φ ψ, φ ≠ ψ →
      IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        ((t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (e φ) (e ψ))
    [∀ φ, IsOpenImmersion (e φ)] (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ) (χ : Φ)
    {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of K))
    (u : SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) gN) :
    ∃ a : SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f,
      u = NeronModelInfra.schemeHomOverComp a ⟨e χ, hef χ⟩ := by
  have hrange : Set.range u.1.base ⊆ Set.range (e χ).base := by
    rintro _ ⟨x, rfl⟩
    have hgx : gN (u.1 x) = (Spec.map (CommRingCat.ofHom (algebraMap R K))) (σ x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, u.2]
    have hx : u.1 x ∈ ⋃ φ, Set.range (e φ).base := by rw [hecov]; trivial
    obtain ⟨ψ, g, hg⟩ := Set.mem_iUnion.mp hx
    have hfg : g ∈ Set.range (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨σ x, ?_⟩
      change _ = f g
      rw [← hef ψ, Scheme.Hom.comp_apply, hg, hgx]
    obtain ⟨z, hz⟩ := hfg
    by_cases hψχ : ψ = χ
    · subst hψχ; exact ⟨g, hg⟩
    · refine ⟨((t ψ χ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) z, ?_⟩
      change ((t ψ χ).hom ≫ pullback.fst f _ ≫ e χ) z = u.1 x
      rw [← Category.assoc, ← (hpb ψ χ hψχ).w, Scheme.Hom.comp_apply, hz, hg]
  refine ⟨⟨IsOpenImmersion.lift (e χ) u.1 hrange, ?_⟩, Subtype.ext (IsOpenImmersion.lift_fac _ _ _).symm⟩
  rw [← hef χ, ← Category.assoc, IsOpenImmersion.lift_fac]
  exact u.2

theorem pt_eq_of_generic_eq [IsSeparated gN] {X : Scheme.{u}} (tX : X ⟶ Spec (CommRingCat.of R)) [Flat tX]
    (h1 h2 : SchemeHomOver tX gN)
    (H : ∀ {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of K)) (q : T ⟶ X)
      (hq : q ≫ tX = σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))),
      GoodReductionJacobian.schemeHomOverComp q hq h1 = GoodReductionJacobian.schemeHomOverComp q hq h2) :
    h1 = h2 := by
  apply NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R K gN tX
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [genericFibreRestrict_coe_comp_fst, genericFibreRestrict_coe_comp_fst]
    exact congrArg Subtype.val (H (pullback.snd tX (specGenericFibreInclusion R K)) (pullback.fst tX _)
      pullback.condition)
  · rw [genericFibreRestrict_coe_comp_snd, genericFibreRestrict_coe_comp_snd]

section Axioms

variable (m : pullback gN gN ⟶ N) (hmg : m ≫ gN = pullback.fst gN gN ≫ gN)
  (ιN : N ⟶ N) (hιg : ιN ≫ gN = gN)

include hef in

theorem mulPt_assoc (hc0 : c 0 0 = L.one _) [Flat f] [IsSeparated gN]
    (hm : ∀ φ ψ : Φ, prodChart e gN hef φ ψ ≫ m = chartMul L c φ ψ ≫ e (φ + ψ))
    (hpb : ∀ φ ψ, φ ≠ ψ →
      IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        ((t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (e φ) (e ψ))
    [∀ φ, IsOpenImmersion (e φ)] (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ)
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (u v w : SchemeHomOver s gN) :
    mulPt gN m hmg s (mulPt gN m hmg s u v) w = mulPt gN m hmg s u (mulPt gN m hmg s v w) := by
  haveI : Flat gN := flat_gN e gN hef hecov

  let tX : pullback (pullback.fst gN gN ≫ gN) gN ⟶ Spec (CommRingCat.of R) :=
    pullback.fst _ _ ≫ pullback.fst gN gN ≫ gN
  haveI : Flat (pullback.fst (pullback.fst gN gN ≫ gN) gN ≫ pullback.fst gN gN ≫ gN) := inferInstance
  let U : SchemeHomOver (pullback.fst (pullback.fst gN gN ≫ gN) gN ≫ pullback.fst gN gN ≫ gN) gN :=
    ⟨pullback.fst _ _ ≫ pullback.fst gN gN, by simp only [Category.assoc]⟩
  let V : SchemeHomOver (pullback.fst (pullback.fst gN gN ≫ gN) gN ≫ pullback.fst gN gN ≫ gN) gN :=
    ⟨pullback.fst _ _ ≫ pullback.snd gN gN, by simp only [Category.assoc, ← pullback.condition]⟩
  let W : SchemeHomOver (pullback.fst (pullback.fst gN gN ≫ gN) gN ≫ pullback.fst gN gN ≫ gN) gN :=
    ⟨pullback.snd _ _, by rw [← pullback.condition]⟩
  have huniv : mulPt gN m hmg _ (mulPt gN m hmg _ U V) W = mulPt gN m hmg _ U (mulPt gN m hmg _ V W) := by
    apply pt_eq_of_generic_eq (K := K) gN _
    intro T' σ q hq
    simp only [mulPt_natural]
    obtain ⟨a, ha⟩ := exists_pt_eq_comp_chart e t gN hef hpb hecov 0 σ (GoodReductionJacobian.schemeHomOverComp q hq U)
    obtain ⟨b, hb⟩ := exists_pt_eq_comp_chart e t gN hef hpb hecov 0 σ (GoodReductionJacobian.schemeHomOverComp q hq V)
    obtain ⟨d, hd⟩ := exists_pt_eq_comp_chart e t gN hef hpb hecov 0 σ (GoodReductionJacobian.schemeHomOverComp q hq W)
    rw [ha, hb, hd]
    simp only [mulPt_chart0 L c e gN hef hc0 m hmg hm, L.mul_assoc]

  let q : T ⟶ pullback (pullback.fst gN gN ≫ gN) gN :=
    pullback.lift (pullback.lift u.1 v.1 (u.2.trans v.2.symm)) w.1
      (by rw [pullback.lift_fst_assoc, u.2, w.2])
  have hq : q ≫ (pullback.fst (pullback.fst gN gN ≫ gN) gN ≫ pullback.fst gN gN ≫ gN) = s := by
    simp only [q, pullback.lift_fst_assoc, u.2]
  have h := congrArg (GoodReductionJacobian.schemeHomOverComp q hq) huniv
  simp only [mulPt_natural] at h
  have eU : GoodReductionJacobian.schemeHomOverComp q hq U = u := Subtype.ext (by simp [q, U])
  have eV : GoodReductionJacobian.schemeHomOverComp q hq V = v := Subtype.ext (by simp [q, V])
  have eW : GoodReductionJacobian.schemeHomOverComp q hq W = w := Subtype.ext (by simp [q, W])
  rw [eU, eV, eW] at h
  exact h

include hef in

theorem mulPt_comm (hL : L.IsCommutative) (hc0 : c 0 0 = L.one _) [Flat f] [IsSeparated gN]
    (hm : ∀ φ ψ : Φ, prodChart e gN hef φ ψ ≫ m = chartMul L c φ ψ ≫ e (φ + ψ))
    (hpb : ∀ φ ψ, φ ≠ ψ →
      IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        ((t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (e φ) (e ψ))
    [∀ φ, IsOpenImmersion (e φ)] (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ)
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver s gN) :
    mulPt gN m hmg s u v = mulPt gN m hmg s v u := by
  haveI : Flat gN := flat_gN e gN hef hecov
  haveI : Flat (pullback.fst gN gN ≫ gN) := inferInstance
  let U : SchemeHomOver (pullback.fst gN gN ≫ gN) gN := ⟨pullback.fst gN gN, rfl⟩
  let V : SchemeHomOver (pullback.fst gN gN ≫ gN) gN := ⟨pullback.snd gN gN, pullback.condition.symm⟩
  have huniv : mulPt gN m hmg _ U V = mulPt gN m hmg _ V U := by
    apply pt_eq_of_generic_eq (K := K) gN _
    intro T' σ q hq
    simp only [mulPt_natural]
    obtain ⟨a, ha⟩ := exists_pt_eq_comp_chart e t gN hef hpb hecov 0 σ (GoodReductionJacobian.schemeHomOverComp q hq U)
    obtain ⟨b, hb⟩ := exists_pt_eq_comp_chart e t gN hef hpb hecov 0 σ (GoodReductionJacobian.schemeHomOverComp q hq V)
    rw [ha, hb]
    simp only [mulPt_chart0 L c e gN hef hc0 m hmg hm, hL.mul_comm]
  let q : T ⟶ pullback gN gN := pullback.lift u.1 v.1 (u.2.trans v.2.symm)
  have hq : q ≫ (pullback.fst gN gN ≫ gN) = s := by simp only [q, pullback.lift_fst_assoc, u.2]
  have h := congrArg (GoodReductionJacobian.schemeHomOverComp q hq) huniv
  simp only [mulPt_natural] at h
  have eU : GoodReductionJacobian.schemeHomOverComp q hq U = u := Subtype.ext (by simp [q, U])
  have eV : GoodReductionJacobian.schemeHomOverComp q hq V = v := Subtype.ext (by simp [q, V])
  rw [eU, eV] at h
  exact h

include hef in

theorem onePt_mulPt (hc0 : c 0 0 = L.one _) [Flat f] [IsSeparated gN]
    (hm : ∀ φ ψ : Φ, prodChart e gN hef φ ψ ≫ m = chartMul L c φ ψ ≫ e (φ + ψ))
    (hpb : ∀ φ ψ, φ ≠ ψ →
      IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        ((t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (e φ) (e ψ))
    [∀ φ, IsOpenImmersion (e φ)] (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ)
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver s gN) :
    mulPt gN m hmg s (onePt L e gN hef s) u = u := by
  haveI : Flat gN := flat_gN e gN hef hecov
  let U : SchemeHomOver gN gN := ⟨𝟙 N, Category.id_comp _⟩
  have huniv : mulPt gN m hmg _ (onePt L e gN hef gN) U = U := by
    apply pt_eq_of_generic_eq (K := K) gN _
    intro T' σ q hq
    simp only [mulPt_natural, onePt_natural]
    obtain ⟨a, ha⟩ := exists_pt_eq_comp_chart e t gN hef hpb hecov 0 σ (GoodReductionJacobian.schemeHomOverComp q hq U)
    rw [ha]
    change mulPt gN m hmg _ (NeronModelInfra.schemeHomOverComp (L.one _) ⟨e 0, hef 0⟩) _ = _
    simp only [mulPt_chart0 L c e gN hef hc0 m hmg hm, L.one_mul]
  have h := congrArg (GoodReductionJacobian.schemeHomOverComp u.1 u.2) huniv
  simp only [mulPt_natural, onePt_natural] at h
  have eU : GoodReductionJacobian.schemeHomOverComp u.1 u.2 U = u := Subtype.ext (Category.comp_id _)
  rw [eU] at h
  exact h

include hef in

theorem mulPt_onePt (hc0 : c 0 0 = L.one _) [Flat f] [IsSeparated gN]
    (hm : ∀ φ ψ : Φ, prodChart e gN hef φ ψ ≫ m = chartMul L c φ ψ ≫ e (φ + ψ))
    (hpb : ∀ φ ψ, φ ≠ ψ →
      IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        ((t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (e φ) (e ψ))
    [∀ φ, IsOpenImmersion (e φ)] (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ)
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver s gN) :
    mulPt gN m hmg s u (onePt L e gN hef s) = u := by
  haveI : Flat gN := flat_gN e gN hef hecov
  let U : SchemeHomOver gN gN := ⟨𝟙 N, Category.id_comp _⟩
  have huniv : mulPt gN m hmg _ U (onePt L e gN hef gN) = U := by
    apply pt_eq_of_generic_eq (K := K) gN _
    intro T' σ q hq
    simp only [mulPt_natural, onePt_natural]
    obtain ⟨a, ha⟩ := exists_pt_eq_comp_chart e t gN hef hpb hecov 0 σ (GoodReductionJacobian.schemeHomOverComp q hq U)
    rw [ha]
    change mulPt gN m hmg _ _ (NeronModelInfra.schemeHomOverComp (L.one _) ⟨e 0, hef 0⟩) = _
    simp only [mulPt_chart0 L c e gN hef hc0 m hmg hm, L.mul_one]
  have h := congrArg (GoodReductionJacobian.schemeHomOverComp u.1 u.2) huniv
  simp only [mulPt_natural, onePt_natural] at h
  have eU : GoodReductionJacobian.schemeHomOverComp u.1 u.2 U = u := Subtype.ext (Category.comp_id _)
  rw [eU] at h
  exact h

include hef in

theorem invPt_mulPt (hc0 : c 0 0 = L.one _) [Flat f] [IsSeparated gN]
    (hm : ∀ φ ψ : Φ, prodChart e gN hef φ ψ ≫ m = chartMul L c φ ψ ≫ e (φ + ψ))
    (hι : ∀ φ : Φ, e φ ≫ ιN = chartInvG L c φ ≫ e (-φ))
    (hpb : ∀ φ ψ, φ ≠ ψ →
      IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        ((t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (e φ) (e ψ))
    [∀ φ, IsOpenImmersion (e φ)] (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ)
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver s gN) :
    mulPt gN m hmg s (invPt gN ιN hιg s u) u = onePt L e gN hef s := by
  haveI : Flat gN := flat_gN e gN hef hecov
  let U : SchemeHomOver gN gN := ⟨𝟙 N, Category.id_comp _⟩
  have huniv : mulPt gN m hmg _ (invPt gN ιN hιg _ U) U = onePt L e gN hef gN := by
    apply pt_eq_of_generic_eq (K := K) gN _
    intro T' σ q hq
    simp only [mulPt_natural, onePt_natural, invPt_natural]
    obtain ⟨a, ha⟩ := exists_pt_eq_comp_chart e t gN hef hpb hecov 0 σ (GoodReductionJacobian.schemeHomOverComp q hq U)
    rw [ha]
    simp only [invPt_chart0 L c e gN hef hc0 ιN hιg hι, mulPt_chart0 L c e gN hef hc0 m hmg hm, L.inv_mul_cancel]
    rfl
  have h := congrArg (GoodReductionJacobian.schemeHomOverComp u.1 u.2) huniv
  simp only [mulPt_natural, onePt_natural, invPt_natural] at h
  have eU : GoodReductionJacobian.schemeHomOverComp u.1 u.2 U = u := Subtype.ext (Category.comp_id _)
  rw [eU] at h
  exact h

end Axioms

end Charts

theorem glueLaw_exists_mul
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (hL : L.IsCommutative)
    [Flat f] [IsSeparated f]
    {Φ : Type u} [AddCommGroup Φ]
    (y : Φ → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) f)
    (c : Φ → Φ → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hc : ∀ φ ψ, Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ (c φ ψ).1 =
      (L.mul _ (L.mul _ (y φ) (y ψ)) (L.inv _ (y (φ + ψ)))).1)
    (hc0 : c 0 0 = L.one _)
    {N : Scheme.{u}} (gN : N ⟶ Spec (CommRingCat.of R)) [IsSeparated gN]
    (e : Φ → (G ⟶ N)) (he : ∀ φ, IsOpenImmersion (e φ)) (hef : ∀ φ, e φ ≫ gN = f)
    (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ)
    (t : Φ → Φ → (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≅
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (ht : ∀ φ ψ, (t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      (L.mul (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))), pullback.condition⟩
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) rfl
            (L.mul _ (y φ) (L.inv _ (y ψ))))).1)
    (hpb : ∀ φ ψ, φ ≠ ψ →
      IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        ((t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (e φ) (e ψ)) :
    ∃ m : pullback gN gN ⟶ N, m ≫ gN = pullback.fst gN gN ≫ gN ∧
      ∀ φ ψ : Φ, pullback.map f f gN gN (e φ) (e ψ) (𝟙 _)
          (by rw [Category.comp_id, hef]) (by rw [Category.comp_id, hef]) ≫ m =
        chartMul L c φ ψ ≫ e (φ + ψ) := by
  haveI := he
  refine ⟨(prodChartCover e gN hef hecov).glueMorphisms (fun i => chartMul L c i.1 i.2 ≫ e (i.1 + i.2))
    (fun i j => ?_), ?_, fun φ ψ => ?_⟩
  · exact overlap_compat L y c e t gN hef hL hc ht hpb hecov i.1 i.2 j.1 j.2
  · apply Scheme.Cover.hom_ext (prodChartCover e gN hef hecov)
    intro i
    rw [Scheme.Cover.ι_glueMorphisms_assoc]
    change (chartMul L c i.1 i.2 ≫ e (i.1 + i.2)) ≫ gN = prodChart e gN hef i.1 i.2 ≫ pullback.fst gN gN ≫ gN
    rw [prodChart_fst_gN, Category.assoc, hef, chartMul_comp_f]
  · exact (prodChartCover e gN hef hecov).ι_glueMorphisms _ _ (φ, ψ)

end GoodReductionJacobian.RelativeGroupLaw.GlueLaw72558c4a
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_glued_charts_mul_eq.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_glued_charts_mul_eq.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_glued_charts_mul_eq.GoodReductionJacobian.RelativeGroupLaw.GlueLaw72558c4a"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_glued_charts_mul_eq.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_glued_charts_mul_eq.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_glued_charts_mul_eq.GoodReductionJacobian"

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (hL : L.IsCommutative)
    [Flat f] [IsSeparated f]
    {Φ : Type u} [AddCommGroup Φ]
    (y : Φ → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) f)
    (c : Φ → Φ → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hc : ∀ φ ψ, Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ (c φ ψ).1 =
      (L.mul _ (L.mul _ (y φ) (y ψ)) (L.inv _ (y (φ + ψ)))).1)
    (hc0 : c 0 0 = L.one _)
    {N : Scheme.{u}} (gN : N ⟶ Spec (CommRingCat.of R)) [IsSeparated gN]
    (e : Φ → (G ⟶ N)) (he : ∀ φ, IsOpenImmersion (e φ)) (hef : ∀ φ, e φ ≫ gN = f)
    (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ)
    (t : Φ → Φ → (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≅
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (ht : ∀ φ ψ, (t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      (L.mul (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))), pullback.condition⟩
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) rfl
            (L.mul _ (y φ) (L.inv _ (y ψ))))).1)
    (hpb : ∀ φ ψ, φ ≠ ψ →
      IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        ((t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (e φ) (e ψ)) :
    ∃ LN : RelativeGroupLaw R gN, LN.IsCommutative ∧
      ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (φ ψ : Φ) (a b : SchemeHomOver s f),
        LN.mul s (NeronModelInfra.schemeHomOverComp a ⟨e φ, hef φ⟩)
            (NeronModelInfra.schemeHomOverComp b ⟨e ψ, hef ψ⟩) =
          NeronModelInfra.schemeHomOverComp
            (L.mul s (L.mul s a b) (GoodReductionJacobian.schemeHomOverComp s (Category.comp_id s) (c φ ψ)))
            ⟨e (φ + ψ), hef (φ + ψ)⟩ := by
  haveI := he
  obtain ⟨m, hmg, hm⟩ :=
    RelativeGroupLaw.GlueLaw72558c4a.glueLaw_exists_mul R K L hL y c hc hc0 gN e he hef hecov t ht hpb
  obtain ⟨ιN, hιg, hι⟩ := RelativeGroupLaw.GlueLaw72558c4a.glueLaw_exists_inv L y c e t gN hef hL hc ht hpb hecov
  refine ⟨{ mul := fun s u v => RelativeGroupLaw.GlueLaw72558c4a.mulPt gN m hmg s u v
            one := fun s => RelativeGroupLaw.GlueLaw72558c4a.onePt L e gN hef s
            inv := fun s u => RelativeGroupLaw.GlueLaw72558c4a.invPt gN ιN hιg s u
            mul_assoc := fun s u v w =>
              RelativeGroupLaw.GlueLaw72558c4a.mulPt_assoc L c e t gN hef m hmg hc0 hm hpb hecov s u v w
            one_mul := fun s u => RelativeGroupLaw.GlueLaw72558c4a.onePt_mulPt L c e t gN hef m hmg hc0 hm hpb hecov s u
            mul_one := fun s u => RelativeGroupLaw.GlueLaw72558c4a.mulPt_onePt L c e t gN hef m hmg hc0 hm hpb hecov s u
            inv_mul_cancel := fun s u =>
              RelativeGroupLaw.GlueLaw72558c4a.invPt_mulPt L c e t gN hef m hmg ιN hιg hc0 hm hι hpb hecov s u
            mul_natural := fun s s' ψ hψ u v => RelativeGroupLaw.GlueLaw72558c4a.mulPt_natural gN m hmg s s' ψ hψ u v },
    fun s u v => RelativeGroupLaw.GlueLaw72558c4a.mulPt_comm L c e t gN hef m hmg hL hc0 hm hpb hecov s u v,
    fun s φ ψ a b => ?_⟩
  exact RelativeGroupLaw.GlueLaw72558c4a.mulPt_chart L c e gN hef m hmg hm s φ ψ a b

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_glued_charts_mul_eq.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_glued_charts_mul_eq.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_glued_charts_mul_eq.GoodReductionJacobian.RelativeGroupLaw.GlueLaw72558c4a"

end S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_glued_charts_mul_eq
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_glued_charts_mul_eq (solution)
