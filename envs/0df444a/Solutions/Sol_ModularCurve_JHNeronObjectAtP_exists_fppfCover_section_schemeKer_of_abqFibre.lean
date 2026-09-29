-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_fppfCover_section_schemeKer_of_abqFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/fcd96197-93df-52c4-b042-fb11f16cac20

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Theorems.Thm_AlgebraicGeometry_SplitTorus_exists_flat_surjective_pow_eq_comp
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_iso_torus_kerPair_abqFibre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve.JHNeronObjectAtP"

namespace ModularCurve
p2m_export "ModularCurve" "JHNeronObjectAtP.LevelData JHNeronObjectAtP JZeroNeronObjectAtP JHNeronObjectAtP.exists_iso_torus_kerPair_abqFibre"
namespace JHNeronObjectAtP
p2m_export "ModularCurve.JHNeronObjectAtP" "LevelData torusFibre abqFibre_flat abqFibre comm abqFibre_mul surjective g separated abqFibre_surjective G toricRank locallyOfFiniteType abqFibre_eq_one_iff L exists_iso_torus_kerPair_abqFibre"
namespace C4b
p2m_open "ModularCurve.JHNeronObjectAtP ModularCurve"

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A}

noncomputable abbrev GA (O : JHNeronObjectAtP p M H hpM A hA Λ) := O.L.baseChange (resPt A ≫ Λ.σA)

noncomputable abbrev AA (O : JHNeronObjectAtP p M H hpM A hA Λ) := Λ.L.baseChange (resPt A ≫ Λ.σA)

noncomputable abbrev ιG (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) :
    (GA O).schemeKer m ⟶ RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) O.g :=
  pullback.fst ((GA O).schemeNsmul m) ((GA O).one (𝟙 _)).1

noncomputable abbrev ιA (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) :
    (AA O).schemeKer m ⟶ RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) Λ.f :=
  pullback.fst ((AA O).schemeNsmul m) ((AA O).one (𝟙 _)).1

theorem ι_comp_str {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ) :
    pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f = L.schemeKerStr n := by
  calc pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f
      = pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ (L.schemeNsmul n ≫ f) := by rw [L.schemeNsmul_over]
    _ = (pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ L.schemeNsmul n) ≫ f := by rw [Category.assoc]
    _ = (pullback.snd (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ (L.one (𝟙 _)).1) ≫ f := by rw [pullback.condition]
    _ = L.schemeKerStr n := by rw [Category.assoc, (L.one (𝟙 _)).2, Category.comp_id]

noncomputable abbrev P (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) : Scheme.{0} :=
  pullback ((AA O).schemeKerStr m) ((AA O).schemeKerStr m)

noncomputable abbrev abqPair (O : JHNeronObjectAtP p M H hpM A hA Λ) :
    RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) O.g ⟶
      pullback (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) :=
  pullback.lift (O.abqFibre 0).1 (O.abqFibre 1).1 ((O.abqFibre 0).2.trans (O.abqFibre 1).2.symm)

noncomputable abbrev jP (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) :
    P O m ⟶ pullback (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) :=
  pullback.map _ _ _ _ (ιA O m) (ιA O m) (𝟙 _) (by rw [Category.comp_id, ι_comp_str]) (by rw [Category.comp_id, ι_comp_str])

noncomputable abbrev U₁ (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) : Scheme.{0} := pullback (jP O m) (abqPair O)
noncomputable abbrev u₁ (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) : U₁ O m ⟶ P O m := pullback.fst _ _
noncomputable abbrev g₁ (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) :
    U₁ O m ⟶ RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) O.g := pullback.snd _ _

scoped instance abqPair_flat (O : JHNeronObjectAtP p M H hpM A hA Λ) : Flat (abqPair O) := O.abqFibre_flat
scoped instance abqPair_surjective (O : JHNeronObjectAtP p M H hpM A hA Λ) : Surjective (abqPair O) := O.abqFibre_surjective

end ModularCurve.JHNeronObjectAtP.C4b
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve.JHNeronObjectAtP P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve.JHNeronObjectAtP.C4b"
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve.JHNeronObjectAtP"
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "JHNeronObjectAtP.LevelData JHNeronObjectAtP JZeroNeronObjectAtP JHNeronObjectAtP.exists_iso_torus_kerPair_abqFibre"
namespace JHNeronObjectAtP
p2m_export "ModularCurve.JHNeronObjectAtP" "LevelData torusFibre abqFibre_flat abqFibre comm abqFibre_mul surjective g separated abqFibre_surjective G toricRank locallyOfFiniteType abqFibre_eq_one_iff L exists_iso_torus_kerPair_abqFibre"
namespace C4b
p2m_open "ModularCurve.JHNeronObjectAtP ModularCurve"

open GoodReductionJacobian.RelativeGroupLaw

namespace IsHom

private theorem _root_.ModularCurve.JHNeronObjectAtP.C4b.IsHom.nsmul {R : Type u} [CommRing R] {X X' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    {f' : X' ⟶ Spec (CommRingCat.of R)} {G : RelativeGroupLaw R f} {G' : RelativeGroupLaw R f'}
    {φ : SchemeHomOver f f'} (h : IsHom G G' φ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (G.nsmul t n x) φ = G'.nsmul t n (NeronModelInfra.schemeHomOverComp x φ) := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero, h.one]
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, h, ih]

end IsHom
p2m_export "ModularCurve.JHNeronObjectAtP.C4b" "IsHom.nsmul"

theorem coe_nsmul {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    (L.nsmul t n x).1 = x.1 ≫ L.schemeNsmul n := by
  have h := L.nsmul_natural f t x.1 x.2 n idPoint
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (idPoint (f := f)) = x := Subtype.ext (Category.comp_id _)
  rw [hx] at h
  rw [← h]
  rfl

theorem nsmul_eq_one_of_factors {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f)
    (a : T ⟶ L.schemeKer n) (hx : x.1 = a ≫ pullback.fst _ _) : L.nsmul t n x = L.one t := by
  have ht : t = a ≫ L.schemeKerStr n := by rw [← x.2, hx, Category.assoc, ι_comp_str]
  subst ht
  apply Subtype.ext
  rw [coe_nsmul, hx, RelativeGroupLaw.one_coe_eq L (a ≫ L.schemeKerStr n), Category.assoc, pullback.condition,
    Category.assoc]

end ModularCurve.JHNeronObjectAtP.C4b
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve.JHNeronObjectAtP P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve.JHNeronObjectAtP.C4b"
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve.JHNeronObjectAtP P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve.JHNeronObjectAtP.C4b"
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve.JHNeronObjectAtP P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve.JHNeronObjectAtP.C4b"

namespace ModularCurve
p2m_export "ModularCurve" "JHNeronObjectAtP.LevelData JHNeronObjectAtP JZeroNeronObjectAtP JHNeronObjectAtP.exists_iso_torus_kerPair_abqFibre"
namespace JHNeronObjectAtP
p2m_export "ModularCurve.JHNeronObjectAtP" "LevelData torusFibre abqFibre_flat abqFibre comm abqFibre_mul surjective g separated abqFibre_surjective G toricRank locallyOfFiniteType abqFibre_eq_one_iff L exists_iso_torus_kerPair_abqFibre"
namespace C4b
p2m_open "ModularCurve.JHNeronObjectAtP ModularCurve"

open GoodReductionJacobian.RelativeGroupLaw

theorem nsmul_eq_pow {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    letI := L.pointGroup t
    L.nsmul t n x = x ^ n := by
  letI := L.pointGroup t
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, pow_zero]; rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, pow_succ, ih]; rfl

theorem kerPair_schemeNsmul_comp_ι {R : Type u} [CommRing R] {X X' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    {f' : X' ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) (G' : RelativeGroupLaw R f')
    (φ : Fin 2 → SchemeHomOver f f') (hφ : ∀ i, IsHom G G' (φ i)) (n : ℕ) :
    (kerPairLaw G G' φ hφ).schemeNsmul n ≫ kerPairι G' φ = kerPairι G' φ ≫ G.schemeNsmul n := by
  have h := IsHom.nsmul (kerPairι_isHom (G := G) (G' := G') (φ := φ) (hφ := hφ)) (kerPairStr G' φ) n idPoint
  have h1 := congrArg Subtype.val h
  rw [NeronModelInfra.schemeHomOverComp_coe, coe_nsmul, coe_nsmul, NeronModelInfra.schemeHomOverComp_coe] at h1
  simpa using h1

noncomputable def schemeKerLift {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (n : ℕ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t f) (hx : G.nsmul t n x = G.one t) : SchemeHomOver t (G.schemeKerStr n) :=
  ⟨pullback.lift x.1 t (by
      rw [← coe_nsmul, hx]
      exact RelativeGroupLaw.one_coe_eq G t),
    pullback.lift_snd _ _ _⟩

theorem schemeKerLift_fst {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (n : ℕ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t f) (hx : G.nsmul t n x = G.one t) :
    (schemeKerLift G n x hx).1 ≫ pullback.fst _ _ = x.1 :=
  pullback.lift_fst _ _ _

end ModularCurve.JHNeronObjectAtP.C4b
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve.JHNeronObjectAtP P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve.JHNeronObjectAtP.C4b"
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve.JHNeronObjectAtP P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve.JHNeronObjectAtP.C4b"
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve.JHNeronObjectAtP P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.ModularCurve.JHNeronObjectAtP.C4b"

open ModularCurve.JHNeronObjectAtP.C4b in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (hΛ : IsProper Λ.f)
    (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) (hm : 0 < m)
    (ψ : (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m ⟶
      pullback ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m))
    (hψ₀ : ψ ≫ pullback.fst _ _ ≫ pullback.fst ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m)
        ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 =
      pullback.fst ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m) ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 ≫
        (O.abqFibre 0).1)
    (hψ₁ : ψ ≫ pullback.snd _ _ ≫ pullback.fst ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m)
        ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 =
      pullback.fst ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m) ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 ≫
        (O.abqFibre 1).1) :
    ∃ (U : Scheme.{0}) (u : U ⟶ pullback ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m)
        ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m))
      (_ : Flat u) (_ : Surjective u) (_ : LocallyOfFinitePresentation u)
      (s : U ⟶ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m), s ≫ ψ = u := by
  classical
  haveI : IsSeparated Λ.f := hΛ.toIsSeparated
  haveI : IsProper Λ.f := hΛ
  haveI : LocallyOfFiniteType Λ.f := inferInstance
  haveI : LocallyOfFiniteType O.g := O.locallyOfFiniteType
  haveI : IsSeparated O.g := O.separated

  haveI : LocallyOfFiniteType (abqPair O ≫ pullback.fst _ _ ≫ RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) := by
    rw [← Category.assoc, pullback.lift_fst, (O.abqFibre 0).2]; infer_instance
  haveI : LocallyOfFiniteType (abqPair O) :=
    locallyOfFiniteType_of_comp (abqPair O) (pullback.fst _ _ ≫ RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f)
  haveI : IsLocallyNoetherian (pullback (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f)) := inferInstance
  haveI : LocallyOfFinitePresentation (abqPair O) := inferInstance
  haveI hflat : Flat (u₁ O m) := inferInstance
  haveI hsurj : Surjective (u₁ O m) := inferInstance
  haveI hlfp : LocallyOfFinitePresentation (u₁ O m) := inferInstance
  have hcond : u₁ O m ≫ jP O m = g₁ O m ≫ abqPair O := pullback.condition
  have hfac0 : g₁ O m ≫ (O.abqFibre 0).1 = u₁ O m ≫ pullback.fst _ _ ≫ ιA O m := by
    have h := congrArg (· ≫ pullback.fst _ _) hcond
    simp only [Category.assoc, pullback.lift_fst] at h
    rw [← h]
  have hfac1 : g₁ O m ≫ (O.abqFibre 1).1 = u₁ O m ≫ pullback.snd _ _ ≫ ιA O m := by
    have h := congrArg (· ≫ pullback.snd _ _) hcond
    simp only [Category.assoc, pullback.lift_snd] at h
    rw [← h]
  have hfac : ∀ i, ∃ a : U₁ O m ⟶ (AA O).schemeKer m, g₁ O m ≫ (O.abqFibre i).1 = a ≫ ιA O m := by
    intro i; fin_cases i
    · exact ⟨u₁ O m ≫ pullback.fst _ _, by change g₁ O m ≫ (O.abqFibre 0).1 = _; rw [hfac0, Category.assoc]⟩
    · exact ⟨u₁ O m ≫ pullback.snd _ _, by change g₁ O m ≫ (O.abqFibre 1).1 = _; rw [hfac1, Category.assoc]⟩

  have F2 : ∃ τ : U₁ O m ⟶ SplitTorus.torusScheme (ResidueField ↥A) O.toricRank,
      τ ≫ SplitTorus.torusStr _ _ = g₁ O m ≫ RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g ∧
      τ ≫ O.torusFibre.1 = ((GA O).nsmul (g₁ O m ≫ RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) m
        ⟨g₁ O m, rfl⟩).1 := by
    let s₁ := g₁ O m ≫ RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g
    let gpt : SchemeHomOver s₁ (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) := ⟨g₁ O m, rfl⟩
    have hker : ∀ i, NeronModelInfra.schemeHomOverComp ((GA O).nsmul s₁ m gpt) (O.abqFibre i) = (AA O).one s₁ := by
      intro i
      rw [IsHom.nsmul (fun t x y => O.abqFibre_mul i t x y) s₁ m gpt]
      obtain ⟨a, ha⟩ := hfac i
      exact nsmul_eq_one_of_factors (AA O) m s₁ _ a ha
    obtain ⟨y, hy⟩ := (O.abqFibre_eq_one_iff s₁ ((GA O).nsmul s₁ m gpt)).mp hker
    exact ⟨y.1, y.2, by rw [← hy]; rfl⟩
  obtain ⟨τ, hτ, hτG⟩ := F2

  obtain ⟨U, c, hc1, hc2, hc3, σ, hσ, hσm⟩ :=
    AlgebraicGeometry.SplitTorus.exists_flat_surjective_pow_eq_comp (S := ResidueField ↥A) O.toricRank m hm
      (g₁ O m ≫ RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) τ hτ

  have F6 : ∃ s : U ⟶ (GA O).schemeKer m, s ≫ ψ = c ≫ u₁ O m := by
    obtain ⟨e, he, hen⟩ := ModularCurve.JHNeronObjectAtP.exists_iso_torus_kerPair_abqFibre p M H hpM A hA Λ hΛ O
    let s₁ := g₁ O m ≫ RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g
    let gpt : SchemeHomOver s₁ (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) := ⟨g₁ O m, rfl⟩
    let t := c ≫ s₁
    let gU : SchemeHomOver t (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) :=
      ⟨c ≫ g₁ O m, by rw [Category.assoc]⟩
    let σT : SchemeHomOver t (torusStr (ResidueField ↥A) O.toricRank) := ⟨σ, hσ⟩
    let σG : SchemeHomOver t (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) :=
      NeronModelInfra.schemeHomOverComp σT O.torusFibre

    have T1 : (GA O).nsmul t m σG = (GA O).nsmul t m gU := by
      apply Subtype.ext
      rw [coe_nsmul, coe_nsmul]
      change (σ ≫ O.torusFibre.1) ≫ _ = (c ≫ g₁ O m) ≫ _
      rw [← he, Category.assoc, Category.assoc, ← kerPair_schemeNsmul_comp_ι (GA O) (AA O) O.abqFibre (fun i => O.abqFibre_mul i) m,
        ← Category.assoc e.hom, hen m,
        Category.assoc, he, ← Category.assoc, hσm, Category.assoc, hτG, coe_nsmul, Category.assoc]

    letI grp := (GA O).pointGroup t
    have hcommG : (GA O).IsCommutative := RelativeGroupLaw.IsCommutative.baseChange (resPt A ≫ Λ.σA) O.comm
    let sPt : SchemeHomOver t (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) := gU * σG⁻¹
    have T2 : (GA O).nsmul t m sPt = (GA O).one t := by
      rw [nsmul_eq_pow]
      change (gU * σG⁻¹) ^ m = 1
      have hc : Commute gU σG⁻¹ := hcommG t gU σG⁻¹
      rw [hc.mul_pow, inv_pow, ← nsmul_eq_pow, ← nsmul_eq_pow, T1]
      exact mul_inv_cancel _
    refine ⟨(schemeKerLift (GA O) m sPt T2).1, ?_⟩

    haveI : IsClosedImmersion ((AA O).one (𝟙 _)).1 := RelativeGroupLaw.isClosedImmersion_one (AA O)
    have hσA : ∀ i, NeronModelInfra.schemeHomOverComp σG (O.abqFibre i) = (AA O).one t := fun i =>
      ((O.abqFibre_eq_one_iff t σG).mpr ⟨σT, rfl⟩) i
    have hsA : ∀ i, NeronModelInfra.schemeHomOverComp sPt (O.abqFibre i) =
        NeronModelInfra.schemeHomOverComp gU (O.abqFibre i) := by
      intro i
      letI grpA := (AA O).pointGroup t
      change NeronModelInfra.schemeHomOverComp ((GA O).mul t gU ((GA O).inv t σG)) (O.abqFibre i) = _
      rw [O.abqFibre_mul i t, RelativeGroupLaw.IsHom.inv (fun t x y => O.abqFibre_mul i t x y) t, hσA i]
      change NeronModelInfra.schemeHomOverComp gU (O.abqFibre i) * ((AA O).one t)⁻¹ = _
      rw [show (AA O).one t = (1 : SchemeHomOver t _) from rfl, inv_one, mul_one]
    apply pullback.hom_ext
    · rw [← cancel_mono (ιA O m), Category.assoc, Category.assoc, hψ₀, ← Category.assoc, schemeKerLift_fst,
        Category.assoc, Category.assoc]
      have h := congrArg Subtype.val (hsA 0)
      rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe] at h
      rw [h]
      obtain ⟨a, ha⟩ := hfac 0
      change (c ≫ g₁ O m) ≫ (O.abqFibre 0).1 = c ≫ u₁ O m ≫ pullback.fst _ _ ≫ ιA O m
      rw [Category.assoc, hfac0]
    · rw [← cancel_mono (ιA O m), Category.assoc, Category.assoc, hψ₁, ← Category.assoc, schemeKerLift_fst,
        Category.assoc, Category.assoc]
      have h := congrArg Subtype.val (hsA 1)
      rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe] at h
      rw [h]
      change (c ≫ g₁ O m) ≫ (O.abqFibre 1).1 = c ≫ u₁ O m ≫ pullback.snd _ _ ≫ ιA O m
      rw [Category.assoc, hfac1]
  obtain ⟨s, hs⟩ := F6
  exact ⟨U, c ≫ u₁ O m, inferInstance, inferInstance, inferInstance, s, hs⟩

end S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre (solution)
