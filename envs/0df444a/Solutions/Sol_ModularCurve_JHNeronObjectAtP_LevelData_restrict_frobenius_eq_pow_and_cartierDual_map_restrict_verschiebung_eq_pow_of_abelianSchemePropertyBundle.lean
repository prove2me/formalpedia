-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.LevelData.restrict_frobenius_eq_pow_and_cartierDual_map_restrict_verschiebung_eq_pow_of_abelianSchemePropertyBundle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/f50fc3fc-afb7-5197-9dad-4e5201adfe28

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_PDivisibleGroup_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk_of_ker_eq_torsionIdeal
import Theorems.Thm_PDivisibleGroup_Hopf_exists_verschiebung_algHom_zmodp
import Theorems.Thm_HopfAlgebra_comp_eq_comp_of_forall_cartierDual_apply_eq_pow_apply_zmodp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_restrict_frobenius_eq_pow_and_cartierDual_map_restrict_verschiebung_eq_pow_of_abelianSchemePropertyBundle
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

namespace QESb

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

theorem ringHom_eq_of_specMap_comp_eq {A B : Type} [CommRing A] [CommRing B] {Y : Scheme.{0}}
    (ι : Spec (CommRingCat.of A) ⟶ Y) [Mono ι] (f g : A →+* B)
    (h : Spec.map (CommRingCat.ofHom f) ≫ ι = Spec.map (CommRingCat.ofHom g) ≫ ι) : f = g := by
  rw [cancel_mono] at h
  simpa using congr_arg CommRingCat.Hom.hom (Spec.map_injective h)

theorem specMap_ofHom_comp {X Y Z : Type} [CommRing X] [CommRing Y] [CommRing Z] (f : X →+* Y) (g : Y →+* Z) :
    Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

section NSMUL

variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {p h : ℕ} (G : PDivisibleGroup R p h) (w : ℕ)
  (ι : Spec (CommRingCat.of (G.level w)) ⟶ X)
  (hιbase : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (G.level w))))
  (hιmul : ∀ (B : Type) [CommRing B] [Algebra R B] (x y : G.Point B w)
    (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : G.level w →ₐ[R] B) : G.level w →+* B)) ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : G.level w →ₐ[R] B) : G.level w →+* B)) ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R B))),
    Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : G.level w →ₐ[R] B) : G.level w →+* B)) ≫ ι =
      (L.mul (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟨_, hx⟩ ⟨_, hy⟩).1)

def tautPt : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (G.level w)))) f := ⟨ι, hιbase⟩

noncomputable def univPt : G.Point (G.level w) w := PDivisibleGroup.Point.ofAlgHom (AlgHom.id R (G.level w))

theorem specMap_univPt_pow (n : ℕ) :
    Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (univPt G w ^ n) : G.level w →ₐ[R] G.level w) :
      G.level w →+* G.level w)) = Spec.map (CommRingCat.ofHom (PDivisibleGroup.Hopf.nsmulAlgHom R (G.level w) n : G.level w →+* G.level w)) := by
  rw [PDivisibleGroup.Point.toAlgHom_pow, univPt, PDivisibleGroup.Point.toAlgHom_ofAlgHom, AlgHom.id_comp]

include hιmul in

theorem nsmul_tautPt_val (n : ℕ) :
    (L.nsmul _ (n + 1) (tautPt G w ι hιbase)).1 =
      Spec.map (CommRingCat.ofHom (PDivisibleGroup.Hopf.nsmulAlgHom R (G.level w) (n + 1) : G.level w →+* G.level w)) ≫ ι := by
  induction n with
  | zero =>
      rw [L.nsmul_one_apply, PDivisibleGroup.Hopf.nsmulAlgHom_one]
      change ι = Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ ι
      rw [CommRingCat.ofHom_id]; erw [Spec.map_id]; rw [Category.id_comp]
  | succ n ih =>
      rw [L.nsmul_succ]
      have hover : ∀ m : ℕ, (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (univPt G w ^ m) :
          G.level w →ₐ[R] G.level w) : G.level w →+* G.level w)) ≫ ι) ≫ f =
          Spec.map (CommRingCat.ofHom (algebraMap R (G.level w))) := by
        intro m
        rw [Category.assoc, hιbase, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        exact (PDivisibleGroup.Point.toAlgHom (univPt G w ^ m)).comp_algebraMap
      have H := hιmul (G.level w) (univPt G w ^ (n + 1)) (univPt G w) (hover (n + 1)) (by simpa using hover 1)
      rw [← pow_succ, specMap_univPt_pow] at H
      rw [H]
      have hid : Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (univPt G w) : G.level w →ₐ[R] G.level w) :
          G.level w →+* G.level w)) = 𝟙 _ := by
        rw [univPt, PDivisibleGroup.Point.toAlgHom_ofAlgHom]
        change Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
        rw [CommRingCat.ofHom_id]; exact Spec.map_id _
      congr 2
      · apply Subtype.ext
        show (L.nsmul _ (n + 1) (tautPt G w ι hιbase)).1 =
          Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (univPt G w ^ (n + 1)) : G.level w →ₐ[R] G.level w) :
            G.level w →+* G.level w)) ≫ ι
        rw [ih, specMap_univPt_pow]
      · apply Subtype.ext
        show ι = Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (univPt G w) : G.level w →ₐ[R] G.level w) :
            G.level w →+* G.level w)) ≫ ι
        rw [hid, Category.id_comp]

include hιbase hιmul in

theorem comp_schemeNsmul (n : ℕ) :
    ι ≫ L.schemeNsmul (n + 1) =
      Spec.map (CommRingCat.ofHom (PDivisibleGroup.Hopf.nsmulAlgHom R (G.level w) (n + 1) : G.level w →+* G.level w)) ≫ ι := by
  rw [← nsmul_tautPt_val L G w ι hιbase hιmul n, RelativeGroupLaw.schemeNsmul]
  have hnat := L.nsmul_natural f (Spec.map (CommRingCat.ofHom (algebraMap R (G.level w)))) ι hιbase (n + 1)
    RelativeGroupLaw.idPoint
  have hpt : GoodReductionJacobian.schemeHomOverComp ι hιbase (RelativeGroupLaw.idPoint (f := f)) = tautPt G w ι hιbase :=
    Subtype.ext (Category.comp_id ι)
  rw [hpt] at hnat
  rw [← hnat]
  rfl

end NSMUL

end QESb

open ModularCurve.JHNeronObjectAtP.LevelData in
open ModularCurve in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)

    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (σp : Spec (CommRingCat.of (ZMod p)) ⟶ base p)

    {h : ℕ} (𝒜 : PDivisibleGroup (baseRing p) p h)
    [Algebra (baseRing p) (ZMod p)]
    (hσp : σp = Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) (ZMod p))))
    (ι' : ∀ v : ℕ, Spec (CommRingCat.of ((𝒜.baseChange (ZMod p)).level v)) ⟶ pullback Λ.f σp)
    (hι'base : ∀ v : ℕ, ι' v ≫ pullback.snd Λ.f σp = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) ((𝒜.baseChange (ZMod p)).level v))))
    (hι'cl : ∀ v : ℕ, IsClosedImmersion (ι' v))
    (hι'p : ∀ (v : ℕ), ∃ h3 : ι' v ≫ (Λ.L.baseChange σp).schemeNsmul (p ^ v) =
          (ι' v ≫ pullback.snd Λ.f σp) ≫ ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1,
      IsIso (pullback.lift (f := (Λ.L.baseChange σp).schemeNsmul (p ^ v)) (g := ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1)
        (ι' v) (ι' v ≫ pullback.snd Λ.f σp) h3))

    (hι'mul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra (ZMod p) B] (x y : (𝒜.baseChange (ZMod p)).Point B v)
        (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v) ≫ pullback.snd Λ.f σp =
          Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)))
        (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v) ≫ pullback.snd Λ.f σp =
          Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))),
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v =
          ((Λ.L.baseChange σp).mul (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) ⟨_, hx⟩ ⟨_, hy⟩).1)

    (hι't : ∀ v : ℕ, Spec.map (CommRingCat.ofHom
          ((𝒜.baseChange (ZMod p)).transition v : (𝒜.baseChange (ZMod p)).level (v + 1) →+* (𝒜.baseChange (ZMod p)).level v)) ≫ ι' (v + 1) = ι' v)

    (F V : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp Λ.f) (RelativeGroupLaw.baseChangeStr σp Λ.f))
    (hF : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p]
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) (RelativeGroupLaw.baseChangeStr σp Λ.f)),
      (schemeHomOverComp x F).1 = Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x.1)
    (hVF : V.1 ≫ F.1 = (Λ.L.baseChange σp).schemeNsmul p)
    (hFV : F.1 ≫ V.1 = (Λ.L.baseChange σp).schemeNsmul p)
    (hVmul : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ZMod p)))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp Λ.f)),
        schemeHomOverComp ((Λ.L.baseChange σp).mul s x y) V =
          (Λ.L.baseChange σp).mul s (schemeHomOverComp x V) (schemeHomOverComp y V))

    (φF φV : ∀ v : ℕ, (𝒜.baseChange (ZMod p)).level v →ₐc[ZMod p] (𝒜.baseChange (ZMod p)).level v)
    (hφF : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (φF v : (𝒜.baseChange (ZMod p)).level v →+* (𝒜.baseChange (ZMod p)).level v)) ≫ ι' v = ι' v ≫ F.1)
    (hφV : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (φV v : (𝒜.baseChange (ZMod p)).level v →+* (𝒜.baseChange (ZMod p)).level v)) ≫ ι' v = ι' v ≫ V.1) :
    (∀ (v : ℕ) (a : (𝒜.baseChange (ZMod p)).level v), φF v a = a ^ p) ∧
    (∀ (v : ℕ) (χ : CartierDual (ZMod p) ((𝒜.baseChange (ZMod p)).level v)), CartierDual.map (φV v) χ = χ ^ p) := by
  classical
  haveI hmono : ∀ v, Mono (ι' v) := fun v => by haveI := hι'cl v; infer_instance

  have hchar : ∀ v : ℕ, CharP ((𝒜.baseChange (ZMod p)).level v) p := fun v => by
    haveI : Nontrivial ((𝒜.baseChange (ZMod p)).level v) := Module.nontrivial_of_finrank_pos (R := ZMod p)
      (by rw [(𝒜.baseChange (ZMod p)).finrank_level v]; exact pow_pos (Nat.Prime.pos Fact.out) _)
    exact charP_of_injective_algebraMap (algebraMap (ZMod p) ((𝒜.baseChange (ZMod p)).level v)).injective p

  have h1 : ∀ (v : ℕ) (a : (𝒜.baseChange (ZMod p)).level v), φF v a = a ^ p := by
    intro v
    haveI := hchar v
    have hpin := hF ((𝒜.baseChange (ZMod p)).level v) ⟨ι' v, hι'base v⟩
    rw [NeronModelInfra.schemeHomOverComp_coe] at hpin
    change ι' v ≫ F.1 = Spec.map (CommRingCat.ofHom (frobenius ((𝒜.baseChange (ZMod p)).level v) p)) ≫ ι' v at hpin
    have heq := QESb.ringHom_eq_of_specMap_comp_eq (ι' v)
      ((φF v : (𝒜.baseChange (ZMod p)).level v →ₐc[ZMod p] (𝒜.baseChange (ZMod p)).level v) : (𝒜.baseChange (ZMod p)).level v →+* (𝒜.baseChange (ZMod p)).level v) (frobenius ((𝒜.baseChange (ZMod p)).level v) p)
      (by rw [hφF v, hpin])
    intro a
    exact (RingHom.congr_fun heq a).trans (frobenius_def p a)
  refine ⟨h1, ?_⟩

  have hrestr : ∀ (v : ℕ) (a : (𝒜.baseChange (ZMod p)).level v), φV v (a ^ p) = PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) ((𝒜.baseChange (ZMod p)).level v) p a := by
    intro v a
    obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos (Nat.Prime.pos Fact.out)).symm⟩
    have hns := QESb.comp_schemeNsmul (Λ.L.baseChange σp) (𝒜.baseChange (ZMod p)) v (ι' v) (hι'base v) (hι'mul v) n
    rw [← hn] at hns
    have heq := QESb.ringHom_eq_of_specMap_comp_eq (ι' v)
      (((φV v : (𝒜.baseChange (ZMod p)).level v →ₐc[ZMod p] (𝒜.baseChange (ZMod p)).level v) : (𝒜.baseChange (ZMod p)).level v →+* (𝒜.baseChange (ZMod p)).level v).comp
        ((φF v : (𝒜.baseChange (ZMod p)).level v →ₐc[ZMod p] (𝒜.baseChange (ZMod p)).level v) : (𝒜.baseChange (ZMod p)).level v →+* (𝒜.baseChange (ZMod p)).level v))
      (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) ((𝒜.baseChange (ZMod p)).level v) p : (𝒜.baseChange (ZMod p)).level v →+* (𝒜.baseChange (ZMod p)).level v)
      (by rw [QESb.specMap_ofHom_comp, Category.assoc, hφF v, ← Category.assoc, hφV v, Category.assoc, hVF, hns])
    have := RingHom.congr_fun heq a
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at this
    rw [← h1 v a]
    exact this

  have htrans : ∀ (v : ℕ) (b : (𝒜.baseChange (ZMod p)).level (v + 1)), (𝒜.baseChange (ZMod p)).transition v (φV (v + 1) b) = φV v ((𝒜.baseChange (ZMod p)).transition v b) := by
    intro v
    have heq := QESb.ringHom_eq_of_specMap_comp_eq (ι' (v + 1))
      ((((𝒜.baseChange (ZMod p)).transition v : (𝒜.baseChange (ZMod p)).level (v + 1) →ₐc[ZMod p] (𝒜.baseChange (ZMod p)).level v) : (𝒜.baseChange (ZMod p)).level (v + 1) →+* (𝒜.baseChange (ZMod p)).level v).comp
        ((φV (v + 1) : (𝒜.baseChange (ZMod p)).level (v + 1) →ₐc[ZMod p] (𝒜.baseChange (ZMod p)).level (v + 1)) : (𝒜.baseChange (ZMod p)).level (v + 1) →+* (𝒜.baseChange (ZMod p)).level (v + 1)))
      (((φV v : (𝒜.baseChange (ZMod p)).level v →ₐc[ZMod p] (𝒜.baseChange (ZMod p)).level v) : (𝒜.baseChange (ZMod p)).level v →+* (𝒜.baseChange (ZMod p)).level v).comp
        (((𝒜.baseChange (ZMod p)).transition v : (𝒜.baseChange (ZMod p)).level (v + 1) →ₐc[ZMod p] (𝒜.baseChange (ZMod p)).level v) : (𝒜.baseChange (ZMod p)).level (v + 1) →+* (𝒜.baseChange (ZMod p)).level v))
      (by rw [QESb.specMap_ofHom_comp, QESb.specMap_ofHom_comp, Category.assoc, Category.assoc, hφV (v + 1), hι't v, hφV v,
            ← Category.assoc, hι't v])
    intro b
    have := RingHom.congr_fun heq b
    simp at this
    exact this
  intro v χ

  obtain ⟨W₀, hW₀1, hW₀2, hW₀3⟩ := PDivisibleGroup.Hopf.exists_verschiebung_algHom_zmodp p ((𝒜.baseChange (ZMod p)).level v)
  obtain ⟨W₁, hW₁1, hW₁2, hW₁3⟩ := PDivisibleGroup.Hopf.exists_verschiebung_algHom_zmodp p ((𝒜.baseChange (ZMod p)).level (v + 1))
  obtain ⟨⟨e, he⟩, -⟩ :=
    PDivisibleGroup.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk_of_ker_eq_torsionIdeal (ZMod p) p h
      (𝒜.baseChange (ZMod p)).level (𝒜.baseChange (ZMod p)).transition (𝒜.baseChange (ZMod p)).transition_surjective (𝒜.baseChange (ZMod p)).finrank_level (𝒜.baseChange (ZMod p)).ker_transition v

  have hnat := HopfAlgebra.comp_eq_comp_of_forall_cartierDual_apply_eq_pow_apply_zmodp p ((𝒜.baseChange (ZMod p)).transition v) W₁ hW₁3 W₀ hW₀3

  have key : ∀ x : (𝒜.baseChange (ZMod p)).level v, φV v x = W₀ x := by
    intro x
    obtain ⟨y, rfl⟩ := (𝒜.baseChange (ZMod p)).transition_surjective v x
    apply e.injective
    apply Subtype.ext
    have lhs : ((e (φV v ((𝒜.baseChange (ZMod p)).transition v y)) :
        ↥(PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) ((𝒜.baseChange (ZMod p)).level (v + 1)) p).range) : (𝒜.baseChange (ZMod p)).level (v + 1)) =
        PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) ((𝒜.baseChange (ZMod p)).level (v + 1)) p (W₁ y) := by
      rw [← htrans v y, he, PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply, ← hW₁1 y, hrestr (v + 1)]
    have rhs : ((e (W₀ ((𝒜.baseChange (ZMod p)).transition v y)) :
        ↥(PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) ((𝒜.baseChange (ZMod p)).level (v + 1)) p).range) : (𝒜.baseChange (ZMod p)).level (v + 1)) =
        PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) ((𝒜.baseChange (ZMod p)).level (v + 1)) p (W₁ y) := by
      have hy := DFunLike.congr_fun hnat y
      simp only [BialgHom.comp_apply] at hy
      rw [← hy, he]
    rw [lhs, rhs]
  ext a
  rw [CartierDual.map_apply, key]
  exact hW₀3 χ a

end S_ModularCurve_JHNeronObjectAtP_LevelData_restrict_frobenius_eq_pow_and_cartierDual_map_restrict_verschiebung_eq_pow_of_abelianSchemePropertyBundle
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_restrict_frobenius_eq_pow_and_cartierDual_map_restrict_verschiebung_eq_pow_of_abelianSchemePropertyBundle (solution)
