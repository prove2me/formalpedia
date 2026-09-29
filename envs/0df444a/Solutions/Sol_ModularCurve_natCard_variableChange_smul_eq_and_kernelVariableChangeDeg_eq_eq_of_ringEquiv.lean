-- Prove2me | solution 1 for ModularCurve.natCard_variableChange_smul_eq_and_kernelVariableChangeDeg_eq_eq_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f3c60928-8c42-56c5-a0d9-3c92781bd722

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_variableChange_smul_eq_and_kernelVariableChangeDeg_eq_eq_of_ringEquiv

set_option autoImplicit false

universe u

open ModularCurve

theorem solution
    {K K' : Type u} [Field K] [Field K'] (σ : K ≃+* K')
    (W : WeierstrassCurve K) {I : Type u} (d : I → ℕ) (T : I → Polynomial K) :
    Nat.card {C : WeierstrassCurve.VariableChange K //
        C • W = W ∧ ∀ i, ModularCurve.kernelVariableChangeDeg C (d i) (T i) = T i} =
      Nat.card {C' : WeierstrassCurve.VariableChange K' //
        C' • (W.map (σ : K →+* K')) = W.map (σ : K →+* K') ∧
          ∀ i, ModularCurve.kernelVariableChangeDeg C' (d i) ((T i).map (σ : K →+* K')) = (T i).map (σ : K →+* K')} := by
  classical

  have hWback : ∀ {R S : Type u} [Field R] [Field S] (f : R →+* S) (g : S →+* R), g.comp f = RingHom.id R →
      ∀ (V : WeierstrassCurve R), (V.map f).map g = V := by
    intro R S _ _ f g hgf V
    rw [WeierstrassCurve.map_map, hgf, WeierstrassCurve.map_id]
  have hCback : ∀ {R S : Type u} [Field R] [Field S] (f : R →+* S) (g : S →+* R), g.comp f = RingHom.id R →
      ∀ (C : WeierstrassCurve.VariableChange R), (C.map f).map g = C := by
    intro R S _ _ f g hgf C
    rw [WeierstrassCurve.VariableChange.map_map, hgf, WeierstrassCurve.VariableChange.map_id]
  have hPback : ∀ {R S : Type u} [Field R] [Field S] (f : R →+* S) (g : S →+* R), g.comp f = RingHom.id R →
      ∀ (P : Polynomial R), (P.map f).map g = P := by
    intro R S _ _ f g hgf P
    rw [Polynomial.map_map, hgf, Polynomial.map_id]
  have hfwd : ∀ {R S : Type u} [Field R] [Field S] (f : R →+* S) (V : WeierstrassCurve R) (e : I → ℕ) (P : I → Polynomial R)
      (C : WeierstrassCurve.VariableChange R),
      (C • V = V ∧ ∀ i, ModularCurve.kernelVariableChangeDeg C (e i) (P i) = P i) →
      ((C.map f) • (V.map f) = V.map f ∧ ∀ i, ModularCurve.kernelVariableChangeDeg (C.map f) (e i) ((P i).map f) = (P i).map f) := by
    intro R S _ _ f V e P C h
    refine ⟨?_, fun i => ?_⟩
    · rw [WeierstrassCurve.map_variableChange, h.1]
    · rw [← ModularCurve.kernelVariableChangeDeg_map, h.2 i]
  have h1 : (σ.symm : K' →+* K).comp (σ : K →+* K') = RingHom.id K := by
    ext x; simp
  have h2 : (σ : K →+* K').comp (σ.symm : K' →+* K) = RingHom.id K' := by
    ext x; simp
  refine Nat.card_congr
    { toFun := fun C => ⟨C.1.map (σ : K →+* K'), hfwd (σ : K →+* K') W d T C.1 C.2⟩
      invFun := fun C' => ⟨C'.1.map (σ.symm : K' →+* K), by
        have h := hfwd (σ.symm : K' →+* K) (W.map (σ : K →+* K')) d (fun i => (T i).map (σ : K →+* K')) C'.1 C'.2
        simp only [hWback _ _ h1, hPback _ _ h1] at h
        exact h⟩
      left_inv := fun C => Subtype.ext (hCback _ _ h1 C.1)
      right_inv := fun C' => Subtype.ext (hCback _ _ h2 C'.1) }

end S_ModularCurve_natCard_variableChange_smul_eq_and_kernelVariableChangeDeg_eq_eq_of_ringEquiv
end P2MW
export P2MW.S_ModularCurve_natCard_variableChange_smul_eq_and_kernelVariableChangeDeg_eq_eq_of_ringEquiv (solution)
