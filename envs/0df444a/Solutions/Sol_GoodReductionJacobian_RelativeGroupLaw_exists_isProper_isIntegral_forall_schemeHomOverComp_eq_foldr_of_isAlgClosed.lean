-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isProper_isIntegral_forall_schemeHomOverComp_eq_foldr_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/06cb6d42-c465-5d15-952e-77cfdebbb151

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isProper_isIntegral_forall_schemeHomOverComp_eq_foldr_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace ProdFoldCurvesSol

variable {k : Type u} [Field k] {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k g)

local notation "S" => Spec (CommRingCat.of k)

def fold {n : ℕ} {C : Fin n → Scheme.{u}} {c : ∀ i : Fin n, C i ⟶ S} (ν : ∀ i : Fin n, SchemeHomOver (c i) g)
    (y : ∀ i : Fin n, SchemeHomOver (𝟙 S) (c i)) : SchemeHomOver (𝟙 S) g :=
  (List.ofFn fun i : Fin n => NeronModelInfra.schemeHomOverComp (y i) (ν i)).foldr
    (fun Q R => L.mul (𝟙 S) Q R) (L.one (𝟙 S))

theorem fold_zero {C : Fin 0 → Scheme.{u}} {c : ∀ i : Fin 0, C i ⟶ S} (ν : ∀ i : Fin 0, SchemeHomOver (c i) g)
    (y : ∀ i : Fin 0, SchemeHomOver (𝟙 S) (c i)) : fold L ν y = L.one (𝟙 S) := by
  simp [fold]

theorem fold_succ {n : ℕ} {C : Fin (n + 1) → Scheme.{u}} {c : ∀ i : Fin (n + 1), C i ⟶ S}
    (ν : ∀ i : Fin (n + 1), SchemeHomOver (c i) g) (y : ∀ i : Fin (n + 1), SchemeHomOver (𝟙 S) (c i)) :
    fold L ν y = L.mul (𝟙 S) (NeronModelInfra.schemeHomOverComp (y 0) (ν 0))
      (fold L (fun i : Fin n => ν i.succ) (fun i : Fin n => y i.succ)) := by
  simp only [fold, List.ofFn_succ, List.foldr_cons]

structure Datum {n : ℕ} (C : Fin n → Scheme.{u}) (c : ∀ i : Fin n, C i ⟶ S) (ν : ∀ i : Fin n, SchemeHomOver (c i) g) where
  X : Scheme.{u}
  x : X ⟶ S
  proper : IsProper x
  integral : IsIntegral X
  V : SchemeHomOver x g
  surj : ∀ P : SchemeHomOver (𝟙 S) x, ∃ y : ∀ i : Fin n, SchemeHomOver (𝟙 S) (c i),
    NeronModelInfra.schemeHomOverComp P V = fold L ν y
  lift : ∀ y : ∀ i : Fin n, SchemeHomOver (𝟙 S) (c i), ∃ P : SchemeHomOver (𝟙 S) x,
    NeronModelInfra.schemeHomOverComp P V = fold L ν y

theorem eq_id_of_over (P : SchemeHomOver (𝟙 S) (𝟙 S)) : P.1 = 𝟙 S := by
  simpa using P.2

def datumZero (C : Fin 0 → Scheme.{u}) (c : ∀ i : Fin 0, C i ⟶ S) (ν : ∀ i : Fin 0, SchemeHomOver (c i) g) :
    Datum L C c ν where
  X := S
  x := 𝟙 S
  proper := inferInstance
  integral := inferInstance
  V := L.one (𝟙 S)
  surj P := ⟨fun i => i.elim0, by
    rw [fold_zero]
    apply Subtype.ext
    show P.1 ≫ (L.one (𝟙 S)).1 = (L.one (𝟙 S)).1
    rw [eq_id_of_over P, Category.id_comp]⟩
  lift y := ⟨⟨𝟙 S, Category.id_comp _⟩, by
    rw [fold_zero]
    apply Subtype.ext
    show 𝟙 S ≫ (L.one (𝟙 S)).1 = (L.one (𝟙 S)).1
    rw [Category.id_comp]⟩

section Step

variable {C₀ : Scheme.{u}} (c₀ : C₀ ⟶ Spec (CommRingCat.of k)) (ν₀ : SchemeHomOver c₀ g)
  {X' : Scheme.{u}} (x' : X' ⟶ Spec (CommRingCat.of k)) (V' : SchemeHomOver x' g)

def stepStr : pullback c₀ x' ⟶ S := pullback.fst c₀ x' ≫ c₀

theorem stepStr_eq : stepStr c₀ x' = pullback.snd c₀ x' ≫ x' := pullback.condition

def V₁ : SchemeHomOver (stepStr c₀ x') g :=
  ⟨pullback.fst c₀ x' ≫ ν₀.1, by rw [Category.assoc, ν₀.2]; rfl⟩

def V₂ : SchemeHomOver (stepStr c₀ x') g :=
  ⟨pullback.snd c₀ x' ≫ V'.1, by rw [Category.assoc, V'.2, stepStr_eq]⟩

def stepV : SchemeHomOver (stepStr c₀ x') g := L.mul (stepStr c₀ x') (V₁ c₀ ν₀ x') (V₂ c₀ x' V')

theorem comp_stepV {T : Scheme.{u}} {t : T ⟶ S} (P : SchemeHomOver t (stepStr c₀ x')) :
    NeronModelInfra.schemeHomOverComp P (stepV L c₀ ν₀ x' V') =
      L.mul t ⟨(P.1 ≫ pullback.fst c₀ x') ≫ ν₀.1, by rw [Category.assoc, ν₀.2, Category.assoc]; exact P.2⟩
        ⟨(P.1 ≫ pullback.snd c₀ x') ≫ V'.1, by
          rw [Category.assoc, V'.2, Category.assoc, ← stepStr_eq]; exact P.2⟩ := by
  have hnat : NeronModelInfra.schemeHomOverComp P (stepV L c₀ ν₀ x' V') =
      GoodReductionJacobian.schemeHomOverComp P.1 P.2 (stepV L c₀ ν₀ x' V') := Subtype.ext rfl
  rw [hnat, stepV, L.mul_natural]
  congr 1

section Instances

variable [IsProper c₀] [IsIntegral C₀] [IsProper x'] [IsIntegral X']

scoped instance : IsProper (stepStr c₀ x') := inferInstanceAs (IsProper (pullback.fst c₀ x' ≫ c₀))

variable [IsAlgClosed k]

scoped instance isIntegral_pullback_step : IsIntegral (pullback c₀ x') := by
  haveI : GeometricallyIntegral x' := geometricallyIntegral_of_isAlgClosed x'
  haveI : IsLocallyNoetherian C₀ := LocallyOfFiniteType.isLocallyNoetherian c₀
  infer_instance

end Instances

end Step

def datumSucc [IsAlgClosed k] {n : ℕ} (C : Fin (n + 1) → Scheme.{u}) (c : ∀ i : Fin (n + 1), C i ⟶ S)
    (hp : ∀ i, IsProper (c i)) (hi : ∀ i, IsIntegral (C i)) (ν : ∀ i : Fin (n + 1), SchemeHomOver (c i) g)
    (D : Datum L (fun i : Fin n => C i.succ) (fun i : Fin n => c i.succ) (fun i : Fin n => ν i.succ)) :
    Datum L C c ν := by
  haveI : IsProper (c 0) := hp 0
  haveI : IsIntegral (C 0) := hi 0
  haveI : IsProper D.x := D.proper
  haveI : IsIntegral D.X := D.integral
  refine
    { X := pullback (c 0) D.x
      x := stepStr (c 0) D.x
      proper := inferInstance
      integral := inferInstance
      V := stepV L (c 0) (ν 0) D.x D.V
      surj := fun P => ?_
      lift := fun y => ?_ }
  ·
    let y₀ : SchemeHomOver (𝟙 S) (c 0) := ⟨P.1 ≫ pullback.fst (c 0) D.x, by rw [Category.assoc]; exact P.2⟩
    let P' : SchemeHomOver (𝟙 S) D.x := ⟨P.1 ≫ pullback.snd (c 0) D.x, by
      rw [Category.assoc, ← stepStr_eq]; exact P.2⟩
    obtain ⟨y', hy'⟩ := D.surj P'
    refine ⟨Fin.cases y₀ y', ?_⟩
    rw [fold_succ, comp_stepV]
    simp only [Fin.cases_zero, Fin.cases_succ]
    rw [← hy']
    rfl
  · obtain ⟨P', hP'⟩ := D.lift fun i => y i.succ
    refine ⟨⟨pullback.lift (y 0).1 P'.1 ((y 0).2.trans P'.2.symm), by
      show pullback.lift (y 0).1 P'.1 _ ≫ (pullback.fst (c 0) D.x ≫ c 0) = 𝟙 S
      rw [← Category.assoc, pullback.lift_fst]; exact (y 0).2⟩, ?_⟩
    rw [fold_succ, comp_stepV, ← hP']
    congr 1
    · apply Subtype.ext
      show (pullback.lift (y 0).1 P'.1 _ ≫ pullback.fst (c 0) D.x) ≫ (ν 0).1 = (y 0).1 ≫ (ν 0).1
      rw [pullback.lift_fst]
    · apply Subtype.ext
      show (pullback.lift (y 0).1 P'.1 _ ≫ pullback.snd (c 0) D.x) ≫ D.V.1 = P'.1 ≫ D.V.1
      rw [pullback.lift_snd]

def datum [IsAlgClosed k] : ∀ (n : ℕ) (C : Fin n → Scheme.{u}) (c : ∀ i : Fin n, C i ⟶ S)
    (_ : ∀ i, IsProper (c i)) (_ : ∀ i, IsIntegral (C i)) (ν : ∀ i : Fin n, SchemeHomOver (c i) g), Datum L C c ν
  | 0, C, c, _, _, ν => datumZero L C c ν
  | n + 1, C, c, hp, hi, ν =>
      datumSucc L C c hp hi ν
        (datum n (fun i : Fin n => C i.succ) (fun i : Fin n => c i.succ) (fun i => hp i.succ) (fun i => hi i.succ)
          (fun i : Fin n => ν i.succ))

end ProdFoldCurvesSol
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isProper_isIntegral_forall_schemeHomOverComp_eq_foldr_of_isAlgClosed.ProdFoldCurvesSol"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isProper_isIntegral_forall_schemeHomOverComp_eq_foldr_of_isAlgClosed.ProdFoldCurvesSol"

open ProdFoldCurvesSol in
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k g)
    {n : ℕ} {C : Fin n → Scheme.{u}} (c : ∀ i : Fin n, C i ⟶ Spec (CommRingCat.of k))
    [∀ i : Fin n, IsProper (c i)] [∀ i : Fin n, IsIntegral (C i)]
    (ν : ∀ i : Fin n, SchemeHomOver (c i) g) :
    ∃ (X : Scheme.{u}) (x : X ⟶ Spec (CommRingCat.of k)) (_ : IsProper x) (_ : IsIntegral X)
      (V : SchemeHomOver x g),
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x,
        ∃ y : ∀ i : Fin n, SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (c i),
          NeronModelInfra.schemeHomOverComp P V =
            (List.ofFn fun i : Fin n => NeronModelInfra.schemeHomOverComp (y i) (ν i)).foldr
              (fun Q R => L.mul (𝟙 (Spec (CommRingCat.of k))) Q R) (L.one (𝟙 (Spec (CommRingCat.of k))))) ∧
      (∀ y : ∀ i : Fin n, SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (c i),
        ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x,
          NeronModelInfra.schemeHomOverComp P V =
            (List.ofFn fun i : Fin n => NeronModelInfra.schemeHomOverComp (y i) (ν i)).foldr
              (fun Q R => L.mul (𝟙 (Spec (CommRingCat.of k))) Q R) (L.one (𝟙 (Spec (CommRingCat.of k))))) := by
  let D := datum L n C c (fun i => inferInstance) (fun i => inferInstance) ν
  exact ⟨D.X, D.x, D.proper, D.integral, D.V, D.surj, D.lift⟩

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isProper_isIntegral_forall_schemeHomOverComp_eq_foldr_of_isAlgClosed
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isProper_isIntegral_forall_schemeHomOverComp_eq_foldr_of_isAlgClosed (solution)
