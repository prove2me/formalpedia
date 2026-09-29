-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.LevelData.exists_bialgHom_specMap_comp_eq_of_isHom_baseChange_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/b131cc81-1a40-509d-b587-02d165bf5fff

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_bialgHom_specMap_comp_eq_of_isHom_baseChange_level

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

namespace N1a

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

end N1a

namespace N1a

section HOMPT

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

include hιbase in

theorem hover {B : Type} [CommRing B] [Algebra R B] (x : G.Point B w) :
    (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : G.level w →ₐ[R] B) : G.level w →+* B)) ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [Category.assoc, hιbase, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (PDivisibleGroup.Point.toAlgHom x).comp_algebraMap

include hιbase hιmul in

theorem specMap_one_comp (B : Type) [CommRing B] [Algebra R B] :
    Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (1 : G.Point B w) : G.level w →ₐ[R] B) : G.level w →+* B)) ≫ ι =
      (L.one (Spec.map (CommRingCat.ofHom (algebraMap R B)))).1 := by
  have h1 := hover G w ι hιbase (1 : G.Point B w)
  have H := hιmul B 1 1 h1 h1
  rw [mul_one] at H
  letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R B)))
  have HP : (⟨_, h1⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R B))) f) *
      (⟨_, h1⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R B))) f) = ⟨_, h1⟩ :=
    Subtype.ext H.symm
  rw [mul_eq_left] at HP
  exact congr_arg Subtype.val HP

include hιbase hιmul in

theorem comp_schemeNsmul_pow_eq_one [Fact p.Prime] :
    ι ≫ L.schemeNsmul (p ^ w) = (ι ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  obtain ⟨n, hn⟩ : ∃ n, p ^ w = n + 1 := ⟨p ^ w - 1, (Nat.succ_pred_eq_of_pos (pow_pos (Nat.Prime.pos Fact.out) w)).symm⟩
  rw [hn, comp_schemeNsmul L G w ι hιbase hιmul n, ← hn]

  have hpow : (PDivisibleGroup.Hopf.nsmulAlgHom R (G.level w) (p ^ w) : G.level w →+* G.level w) =
      ((PDivisibleGroup.Point.toAlgHom (1 : G.Point (G.level w) w) : G.level w →ₐ[R] G.level w) : G.level w →+* G.level w) := by
    rw [G.nsmulAlgHom_pow_level w]
    rfl
  rw [hpow, specMap_one_comp L G w ι hιbase hιmul (G.level w), hιbase]
  have := L.one_natural (𝟙 (Spec (CommRingCat.of R))) (Spec.map (CommRingCat.ofHom (algebraMap R (G.level w))))
    (Spec.map (CommRingCat.ofHom (algebraMap R (G.level w)))) (Category.comp_id _)
  rw [← this]
  rfl

end HOMPT

end N1a

namespace N1a

section CONV

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h) (w : ℕ)

theorem toAlgHom_includeLeft_mul_includeRight :
    PDivisibleGroup.Point.toAlgHom ((PDivisibleGroup.Point.ofAlgHom (Algebra.TensorProduct.includeLeft :
        G.level w →ₐ[R] G.level w ⊗[R] G.level w) : G.Point (G.level w ⊗[R] G.level w) w) *
      PDivisibleGroup.Point.ofAlgHom Algebra.TensorProduct.includeRight) =
      Bialgebra.comulAlgHom R (G.level w) := by
  apply AlgHom.ext
  intro a
  rw [PDivisibleGroup.Point.mul_apply, PDivisibleGroup.Point.toAlgHom_ofAlgHom, PDivisibleGroup.Point.toAlgHom_ofAlgHom,
    Algebra.TensorProduct.lift_includeLeft_includeRight, Bialgebra.comulAlgHom_apply, AlgHom.id_apply]

theorem toAlgHom_includeLeft_comp_mul_includeRight_comp {p' h' : ℕ} (G' : PDivisibleGroup R p' h') (w' : ℕ)
    (ρ : G'.level w' →ₐ[R] G.level w) :
    PDivisibleGroup.Point.toAlgHom ((PDivisibleGroup.Point.ofAlgHom ((Algebra.TensorProduct.includeLeft :
        G.level w →ₐ[R] G.level w ⊗[R] G.level w).comp ρ) : G'.Point (G.level w ⊗[R] G.level w) w') *
      PDivisibleGroup.Point.ofAlgHom ((Algebra.TensorProduct.includeRight : G.level w →ₐ[R] G.level w ⊗[R] G.level w).comp ρ)) =
      (Algebra.TensorProduct.map ρ ρ).comp (Bialgebra.comulAlgHom R (G'.level w')) := by
  apply AlgHom.ext
  intro a
  rw [PDivisibleGroup.Point.mul_apply, PDivisibleGroup.Point.toAlgHom_ofAlgHom, PDivisibleGroup.Point.toAlgHom_ofAlgHom,
    AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro x y
  simp [Algebra.TensorProduct.lift_tmul]

end CONV

end N1a

open ModularCurve.JHNeronObjectAtP.LevelData in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (σp : Spec (CommRingCat.of (ZMod p)) ⟶ ModularCurve.JZeroNeronObjectAtP.base p)

    {hΛ : ℕ} (𝒜 : PDivisibleGroup (ModularCurve.JZeroNeronObjectAtP.baseRing p) p hΛ)
    [Algebra (ModularCurve.JZeroNeronObjectAtP.baseRing p) (ZMod p)]
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

    (Rh : Type) [CommRing Rh] [Algebra Rh (ZMod p)] {h : ℕ} (𝒢 : PDivisibleGroup Rh p h) (v : ℕ)
    (φ : Spec (CommRingCat.of (ZMod p ⊗[Rh] 𝒢.level v)) ⟶ pullback Λ.f σp)
    (hφbase : φ ≫ pullback.snd Λ.f σp = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v))))
    (hφmul : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] (x y : (𝒢.baseChange (ZMod p)).Point B v)
        (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : (𝒢.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒢.baseChange (ZMod p)).level v →+* B)) ≫ φ) ≫ pullback.snd Λ.f σp =
          Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)))
        (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : (𝒢.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒢.baseChange (ZMod p)).level v →+* B)) ≫ φ) ≫ pullback.snd Λ.f σp =
          Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))),
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : (𝒢.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒢.baseChange (ZMod p)).level v →+* B)) ≫ φ =
          ((Λ.L.baseChange σp).mul (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) ⟨_, hx⟩ ⟨_, hy⟩).1) :
    ∃ ρ : (𝒜.baseChange (ZMod p)).level v →ₐc[ZMod p] (𝒢.baseChange (ZMod p)).level v,
      Spec.map (CommRingCat.ofHom (ρ : (𝒜.baseChange (ZMod p)).level v →+* (𝒢.baseChange (ZMod p)).level v)) ≫ ι' v = φ := by
  classical
  haveI : Mono (ι' v) := by haveI := hι'cl v; infer_instance

  set φ' : Spec (CommRingCat.of ((𝒢.baseChange (ZMod p)).level v)) ⟶ pullback Λ.f σp := φ with hφ'

  have h3 := N1a.comp_schemeNsmul_pow_eq_one (Λ.L.baseChange σp) (𝒢.baseChange (ZMod p)) v φ' hφbase hφmul
  obtain ⟨h3', hiso⟩ := hι'p v
  set jv := pullback.lift (f := (Λ.L.baseChange σp).schemeNsmul (p ^ v))
    (g := ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1) (ι' v) (ι' v ≫ pullback.snd Λ.f σp) h3' with hjv
  haveI : IsIso jv := hiso
  let κ := pullback.lift (f := (Λ.L.baseChange σp).schemeNsmul (p ^ v))
    (g := ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1) φ' (φ' ≫ pullback.snd Λ.f σp) h3
  let ρsch : Spec (CommRingCat.of ((𝒢.baseChange (ZMod p)).level v)) ⟶ Spec (CommRingCat.of ((𝒜.baseChange (ZMod p)).level v)) :=
    κ ≫ inv jv
  have hjfst : jv ≫ pullback.fst _ _ = ι' v := pullback.lift_fst _ _ _
  have hρsch : ρsch ≫ ι' v = φ' := by
    simp only [ρsch, Category.assoc]
    rw [← hjfst, IsIso.inv_hom_id_assoc, pullback.lift_fst]

  let ρr : (𝒜.baseChange (ZMod p)).level v →+* (𝒢.baseChange (ZMod p)).level v := (Spec.preimage ρsch).hom
  have hρr : Spec.map (CommRingCat.ofHom ρr) = ρsch := by
    simp only [ρr, CommRingCat.ofHom_hom]; exact Spec.map_preimage ρsch
  have hcomm : ρr.comp (algebraMap (ZMod p) ((𝒜.baseChange (ZMod p)).level v)) = algebraMap (ZMod p) ((𝒢.baseChange (ZMod p)).level v) := by
    have key : Spec.map (CommRingCat.ofHom (ρr.comp (algebraMap (ZMod p) ((𝒜.baseChange (ZMod p)).level v)))) =
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) ((𝒢.baseChange (ZMod p)).level v))) := by
      rw [N1a.specMap_ofHom_comp, hρr, ← hι'base v, ← Category.assoc, hρsch]
      exact hφbase
    simpa using congr_arg CommRingCat.Hom.hom (Spec.map_injective key)
  let ρa : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] (𝒢.baseChange (ZMod p)).level v :=
    { ρr with commutes' := fun r => RingHom.congr_fun hcomm r }
  have hρa : (ρa : (𝒜.baseChange (ZMod p)).level v →+* (𝒢.baseChange (ZMod p)).level v) = ρr := rfl

  have hpt : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] (x : (𝒢.baseChange (ZMod p)).Point B v),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom
        ((PDivisibleGroup.Point.toAlgHom x).comp ρa) : (𝒜.baseChange (ZMod p)).Point B v) :
          (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v =
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : (𝒢.baseChange (ZMod p)).level v →ₐ[ZMod p] B) :
        (𝒢.baseChange (ZMod p)).level v →+* B)) ≫ φ' := by
    intro B _ _ x
    rw [PDivisibleGroup.Point.toAlgHom_ofAlgHom]
    change Spec.map (CommRingCat.ofHom (((PDivisibleGroup.Point.toAlgHom x : (𝒢.baseChange (ZMod p)).level v →ₐ[ZMod p] B) :
        (𝒢.baseChange (ZMod p)).level v →+* B).comp ρr)) ≫ ι' v = _
    rw [N1a.specMap_ofHom_comp, Category.assoc, hρr, hρsch]

  have hmult : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] (x y : (𝒢.baseChange (ZMod p)).Point B v),
      ((PDivisibleGroup.Point.toAlgHom ((PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp ρa) :
          (𝒜.baseChange (ZMod p)).Point B v) * PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp ρa)) :
          (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B) =
      ((PDivisibleGroup.Point.toAlgHom (x * y) : (𝒢.baseChange (ZMod p)).level v →ₐ[ZMod p] B) :
          (𝒢.baseChange (ZMod p)).level v →+* B).comp ρr := by
    intro B _ _ x y
    apply N1a.ringHom_eq_of_specMap_comp_eq (ι' v)
    have hx := N1a.hover (f := pullback.snd Λ.f σp) (𝒢.baseChange (ZMod p)) v φ' hφbase x
    have hy := N1a.hover (f := pullback.snd Λ.f σp) (𝒢.baseChange (ZMod p)) v φ' hφbase y
    have hx' := N1a.hover (f := pullback.snd Λ.f σp) (𝒜.baseChange (ZMod p)) v (ι' v) (hι'base v)
      (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp ρa))
    have hy' := N1a.hover (f := pullback.snd Λ.f σp) (𝒜.baseChange (ZMod p)) v (ι' v) (hι'base v)
      (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp ρa))
    rw [hι'mul v B _ _ hx' hy', N1a.specMap_ofHom_comp, Category.assoc, hρr, hρsch, hφmul B x y hx hy]
    congr 2
    · exact Subtype.ext (hpt B x)
    · exact Subtype.ext (hpt B y)

  have hcomul : (Algebra.TensorProduct.map ρa ρa).comp (Bialgebra.comulAlgHom (ZMod p) ((𝒜.baseChange (ZMod p)).level v)) =
      (Bialgebra.comulAlgHom (ZMod p) ((𝒢.baseChange (ZMod p)).level v)).comp ρa := by
    have H := hmult ((𝒢.baseChange (ZMod p)).level v ⊗[ZMod p] (𝒢.baseChange (ZMod p)).level v)
      (PDivisibleGroup.Point.ofAlgHom Algebra.TensorProduct.includeLeft)
      (PDivisibleGroup.Point.ofAlgHom Algebra.TensorProduct.includeRight)
    rw [PDivisibleGroup.Point.toAlgHom_ofAlgHom, PDivisibleGroup.Point.toAlgHom_ofAlgHom,
      N1a.toAlgHom_includeLeft_comp_mul_includeRight_comp ((𝒢.baseChange (ZMod p))) v (𝒜.baseChange (ZMod p)) v ρa,
      N1a.toAlgHom_includeLeft_mul_includeRight] at H
    apply AlgHom.coe_ringHom_injective
    rw [H, AlgHom.comp_toRingHom, hρa]

  have hcounit : (Bialgebra.counitAlgHom (ZMod p) ((𝒢.baseChange (ZMod p)).level v)).comp ρa =
      Bialgebra.counitAlgHom (ZMod p) ((𝒜.baseChange (ZMod p)).level v) := by
    have u1 := N1a.specMap_one_comp (Λ.L.baseChange σp) (𝒢.baseChange (ZMod p)) v φ' hφbase hφmul (ZMod p)
    have u2 := N1a.specMap_one_comp (Λ.L.baseChange σp) (𝒜.baseChange (ZMod p)) v (ι' v) (hι'base v) (hι'mul v) (ZMod p)
    rw [← hρsch, ← hρr, ← Category.assoc, ← N1a.specMap_ofHom_comp] at u1
    have heq := N1a.ringHom_eq_of_specMap_comp_eq (ι' v) _ _ (u1.trans u2.symm)

    apply AlgHom.coe_ringHom_injective
    rw [AlgHom.comp_toRingHom, hρa]
    convert heq using 1
    rfl
    rfl
  refine ⟨BialgHom.ofAlgHom ρa hcounit hcomul, ?_⟩
  change Spec.map (CommRingCat.ofHom ρr) ≫ ι' v = φ'
  rw [hρr, hρsch]

end S_ModularCurve_JHNeronObjectAtP_LevelData_exists_bialgHom_specMap_comp_eq_of_isHom_baseChange_level
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_bialgHom_specMap_comp_eq_of_isHom_baseChange_level (solution)
