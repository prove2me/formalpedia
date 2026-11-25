-- Prove2me | solution 1 for HcInf.cayley_set_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:13.242997+00:00
-- url     : https://prove2.me/submissions/96acf04d-0cda-46c2-b8e2-5af04dc0f75b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayK
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExOm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayleyInverseMeasurable
import Theorems.Thm_HcInf_cayley_inverse_iff
import Theorems.Thm_HcInf_cayley_inverse_measurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HcInf
open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace HcInf
theorem _root_.solution : CaySUnivMeas := by
  intro P Q
  have hmat : Continuous (UpqT.mat (P := P) (Q := Q)) := (isInducing_mat P Q).continuous
  set C : Set (UpqT P Q × lieU P Q) := {p | UpqT.mat p.1 *
    ((1 + 1) - ((p.2 : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) =
      (1 + 1) + ((p.2 : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)}
  have hC : IsClosed C := by
    have hv : Continuous fun p : UpqT P Q × lieU P Q =>
        ((p.2 : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
      continuous_subtype_val.comp continuous_snd
    exact isClosed_eq ((hmat.comp continuous_fst).matrix_mul (continuous_const.sub hv))
      (continuous_const.add hv)
  have e : cayS (Set.univ : Set (lieU P Q)) = (fun g => (g, cayInv P Q g)) ⁻¹' C := by
    ext g
    constructor
    · rintro ⟨X, -, h⟩
      show UpqT.mat g * ((1 + 1) - ((cayInv P Q g : lieU P Q) :
          Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) =
        (1 + 1) + ((cayInv P Q g : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)
      rw [cayley_inverse_iff P Q g X h]
      exact h
    · intro h
      exact ⟨cayInv P Q g, Set.mem_univ _, h⟩
  rw [e]
  exact (measurable_id.prodMk (cayley_inverse_measurable P Q)) hC.measurableSet
end HcInf
