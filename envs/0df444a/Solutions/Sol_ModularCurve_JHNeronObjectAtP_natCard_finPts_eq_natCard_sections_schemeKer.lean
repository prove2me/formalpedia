-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.natCard_finPts_eq_natCard_sections_schemeKer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/25cfded4-7b93-54bc-a847-5d8f63e04170

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_mem_finPts_iff_and_isTorsionPoint_section_and_specialPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_natCard_finPts_eq_natCard_sections_schemeKer

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

namespace P125

universe u

theorem nsmul_coe {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) : (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have h := G.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hx] at h
  rw [← h]
  rfl

theorem baseChangePointToBase_nsmul {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ)
    (x : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι f)) :
    RelativeGroupLaw.baseChangePointToBase ι ((G.baseChange ι).nsmul t' n x) =
      G.nsmul _ n (RelativeGroupLaw.baseChangePointToBase ι x) := by
  induction n with
  | zero => exact RelativeGroupLaw.baseChangePointToBase_one ι G t'
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.baseChangePointToBase_mul, ih]

end P125

open P125 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) :
    Nat.card ↥(O.finPts m) =
      Nat.card {s : Spec (CommRingCat.of ↥A) ⟶ (O.L.baseChange Λ.σA).schemeKer m //
        s ≫ (O.L.baseChange Λ.σA).schemeKerStr m = 𝟙 _} := by
  classical

  set LA := O.L.baseChange Λ.σA with hLA
  let SA : Scheme.{0} := Spec (CommRingCat.of ↥A)

  let Tz := {z : SchemeHomOver (𝟙 SA) (RelativeGroupLaw.baseChangeStr Λ.σA O.g) // LA.IsTorsionPoint (𝟙 SA) m z}
  have hfst : pullback.fst (LA.schemeNsmul m) (LA.one (𝟙 SA)).1 ≫ RelativeGroupLaw.baseChangeStr Λ.σA O.g =
      pullback.snd (LA.schemeNsmul m) (LA.one (𝟙 SA)).1 := by
    calc pullback.fst (LA.schemeNsmul m) (LA.one (𝟙 SA)).1 ≫ RelativeGroupLaw.baseChangeStr Λ.σA O.g
        = pullback.fst (LA.schemeNsmul m) (LA.one (𝟙 SA)).1 ≫ LA.schemeNsmul m ≫
            RelativeGroupLaw.baseChangeStr Λ.σA O.g := by rw [LA.schemeNsmul_over]
      _ = (pullback.snd (LA.schemeNsmul m) (LA.one (𝟙 SA)).1 ≫ (LA.one (𝟙 SA)).1) ≫
            RelativeGroupLaw.baseChangeStr Λ.σA O.g := by rw [← Category.assoc, pullback.condition]
      _ = pullback.snd (LA.schemeNsmul m) (LA.one (𝟙 SA)).1 := by
            rw [Category.assoc, (LA.one (𝟙 SA)).2, Category.comp_id]
  let e1 : {s : SA ⟶ LA.schemeKer m // s ≫ LA.schemeKerStr m = 𝟙 _} ≃ Tz :=
    { toFun := fun s => ⟨⟨s.1 ≫ pullback.fst _ _, by rw [Category.assoc, hfst]; exact s.2⟩, by
        apply Subtype.ext
        rw [nsmul_coe]
        show (s.1 ≫ pullback.fst _ _) ≫ LA.schemeNsmul m = (LA.one (𝟙 SA)).1
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        have := s.2
        rw [this, Category.id_comp]⟩
      invFun := fun z => ⟨pullback.lift z.1.1 (𝟙 _) (by
          have h := congrArg Subtype.val z.2
          rw [nsmul_coe] at h
          rw [h, Category.id_comp]), pullback.lift_snd _ _ _⟩
      left_inv := fun s => by
        apply Subtype.ext
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
        · rw [pullback.lift_snd]; exact s.2.symm
      right_inv := fun z => Subtype.ext (Subtype.ext (pullback.lift_fst _ _ _)) }

  let Ty := {y : SchemeHomOver (𝟙 SA ≫ Λ.σA) O.g // O.L.IsTorsionPoint _ m y}
  let e2 : Tz ≃ Ty := (RelativeGroupLaw.baseChangePointEquiv Λ.σA (𝟙 SA)).subtypeEquiv (fun z => by
    show LA.nsmul _ m z = LA.one _ ↔ O.L.nsmul _ m (RelativeGroupLaw.baseChangePointToBase Λ.σA z) = O.L.one _
    rw [← baseChangePointToBase_nsmul, ← RelativeGroupLaw.baseChangePointToBase_one Λ.σA O.L (𝟙 SA)]
    exact ⟨fun h => by rw [h], fun h => (RelativeGroupLaw.baseChangePointEquiv Λ.σA (𝟙 SA)).injective h⟩)

  have hbar : barPt A ≫ (𝟙 SA ≫ Λ.σA) = genPt p := by rw [Category.id_comp]; exact Λ.hσA
  let res : SchemeHomOver (𝟙 SA ≫ Λ.σA) O.g → SchemeHomOver (genPt p) O.g :=
    GoodReductionJacobian.schemeHomOverComp (barPt A) hbar
  have hker : RingHom.ker (A.subtype) ≤ nilradical ↥A := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (A.subtype_injective)]
    exact bot_le
  haveI hdom : IsDominant (barPt A) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr hker⟩
  haveI : IsSeparated O.g := O.separated
  have res_inj : ∀ y y' : SchemeHomOver (𝟙 SA ≫ Λ.σA) O.g, res y = res y' → y = y' := by
    intro y y' h
    apply Subtype.ext
    exact ext_of_isDominant_of_isSeparated O.g (y.2.trans y'.2.symm) (barPt A) (congrArg Subtype.val h)
  have res_nsmul : ∀ (n : ℕ) (y : SchemeHomOver (𝟙 SA ≫ Λ.σA) O.g), res (O.L.nsmul _ n y) = O.L.nsmul _ n (res y) :=
    fun n y => O.L.nsmul_natural _ _ (barPt A) hbar n y
  have res_one : res (O.L.one _) = O.L.one _ := O.L.one_natural _ _ (barPt A) hbar

  have pts_zero : O.pts 0 = O.L.one (genPt p) := by
    letI := O.L.pointGroup (genPt p)
    have h : O.pts 0 * O.pts 0 = O.pts 0 := by
      have := O.pts_add 0 0
      rw [add_zero] at this
      exact this.symm
    exact mul_eq_left.mp h
  have pts_nsmul : ∀ (n : ℕ) (x : JH M H), O.pts (n • x) = O.L.nsmul (genPt p) n (O.pts x) := by
    intro n x
    induction n with
    | zero => rw [zero_nsmul, RelativeGroupLaw.nsmul_zero]; exact pts_zero
    | succ n ih => rw [succ_nsmul, O.pts_add, ih, RelativeGroupLaw.nsmul_succ]
  have mem_tors : ∀ x : JH M H, x ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) m ↔ m • x = 0 := by
    intro x
    rw [Pic0.mem_torsion, natCast_zsmul]
  let F := {x : JH M H // x ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) m ∧ ExtendsToPlace A Λ.σA (O.pts x)}
  let φ : Ty → F := fun y => ⟨O.pts.symm (res y.1), by
    refine ⟨(mem_tors _).2 ?_, ?_⟩
    · apply O.pts.injective
      rw [pts_nsmul, Equiv.apply_symm_apply, ← res_nsmul, y.2, res_one, pts_zero]
    · exact ⟨⟨y.1.1, by simpa only [Category.id_comp] using y.1.2⟩, by rw [Equiv.apply_symm_apply]; rfl⟩⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro y y' h
      have h1 : O.pts.symm (res y.1) = O.pts.symm (res y'.1) := congrArg Subtype.val h
      exact Subtype.ext (res_inj _ _ (O.pts.symm.injective h1))
    · intro x
      obtain ⟨s, hs⟩ := x.2.2
      let y : SchemeHomOver (𝟙 SA ≫ Λ.σA) O.g := ⟨s.1, by rw [Category.id_comp]; exact s.2⟩
      have hy : res y = O.pts x.1 := Subtype.ext hs.symm
      have hty : O.L.IsTorsionPoint _ m y := by
        apply res_inj
        rw [res_nsmul, res_one, hy, ← pts_nsmul, ((mem_tors _).1 x.2.1), pts_zero]
      refine ⟨⟨y, hty⟩, ?_⟩
      apply Subtype.ext
      show O.pts.symm (res y) = x.1
      rw [hy, Equiv.symm_apply_apply]

  let e4 : F ≃ ↥(O.finPts m) := Equiv.subtypeEquivRight (fun x =>
    ((ModularCurve.JHNeronObjectAtP.mem_finPts_iff_and_isTorsionPoint_section_and_specialPt p M H hpM A hA Λ O m).1 x).symm)
  rw [Nat.card_congr e1, Nat.card_congr e2, Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_congr e4]

end S_ModularCurve_JHNeronObjectAtP_natCard_finPts_eq_natCard_sections_schemeKer
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_natCard_finPts_eq_natCard_sections_schemeKer (solution)
