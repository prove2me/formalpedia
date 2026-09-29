-- Prove2me | solution 1 for NumberField.TateGlobal.exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/693d40a6-16d2-5fbd-b59a-6afcc4176e3a

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_M4aHerbrand_GenuineBeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_TateGlobal_exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap.NumberField.TateGlobal NumberField.AdelicLevel AutomorphicForm M4aHerbrand.Bridge"

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing AdeleRing"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "localChar"
namespace WfRestrict
p2m_open "NumberField.TateGlobal NumberField"

variable (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] [Algebra E K]

def restrict (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ :=
  μ.comp (Units.map (genuineβ E K : AdeleRing (𝓞 E) E →* AdeleRing (𝓞 K) K))

theorem restrict_apply (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (x : (AdeleRing (𝓞 E) E)ˣ) :
    restrict E K μ x = μ (Units.map (genuineβ E K : AdeleRing (𝓞 E) E →* AdeleRing (𝓞 K) K) x) := rfl

theorem isIdeleClassChar_restrict (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsIdeleClassChar (𝓞 K) K μ) :
    IsIdeleClassChar (𝓞 E) E (restrict E K μ) := by
  intro u
  rw [restrict_apply]
  have : Units.map (genuineβ E K : AdeleRing (𝓞 E) E →* AdeleRing (𝓞 K) K)
      (Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* AdeleRing (𝓞 E) E) u) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
        (Units.map (algebraMap E K : E →* K) u) := by
    apply Units.ext
    simp only [Units.coe_map, MonoidHom.coe_coe]
    exact genuineβ_compat E K (u : E)
  rw [this]
  exact hμ _

theorem continuous_restrict (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hcont : Continuous μ) :
    Continuous (restrict E K μ) :=
  hcont.comp (Units.continuous_map (continuous_genuineβ E K))

def ideleAt (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F) (localUnit (𝓞 F) F v t)

theorem localChar_eq (F : Type) [Field F] [NumberField F] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) : localChar χ v t = χ (ideleAt F v t) := rfl

theorem val_ideleAt (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    ((ideleAt F v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) =
      ((1 : InfiniteAdeleRing F), ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) :=
  rfl

def upAt (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 K)) (x : (v.adicCompletion E)ˣ) : (w.1.adicCompletion K)ˣ :=
  Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion K)).toMonoidHom x

theorem finiteConorm_localUnit (v : HeightOneSpectrum (𝓞 E)) [Fintype (v.Extension (𝓞 K))] (x : (v.adicCompletion E)ˣ) :
    finiteConorm (𝓞 E) E K (𝓞 K) ((localUnit (𝓞 E) E v x : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) =
      ∏ w : v.Extension (𝓞 K),
        ((localUnit (𝓞 K) K w.1 (upAt E K v w x) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) := by
  classical
  refine FiniteAdeleRing.ext K fun w' => ?_
  rw [finiteConorm_apply]

  have heval : (∏ w : v.Extension (𝓞 K),
      ((localUnit (𝓞 K) K w.1 (upAt E K v w x) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K)) w' =
      ∏ w : v.Extension (𝓞 K),
        ((localUnit (𝓞 K) K w.1 (upAt E K v w x) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w' := by
    rw [← finAdeleEval_apply (𝓞 K) K w', map_prod]
    rfl
  rw [heval]
  by_cases hw' : w'.under (𝓞 E) = v
  · subst hw'
    rw [localUnit_apply_self]
    symm
    refine (@Finset.prod_eq_single ((w'.under (𝓞 E)).Extension (𝓞 K)) _ _ Finset.univ _ ⟨w', rfl⟩ ?_ ?_).trans ?_
    · intro w _ hw
      apply localUnit_apply_of_ne
      intro h
      exact hw (Subtype.ext h.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
    · rw [localUnit_apply_self]
      rfl
  · rw [localUnit_apply_of_ne _ _ _ _ hw', map_one]
    symm
    refine Finset.prod_eq_one fun w _ => ?_
    apply localUnit_apply_of_ne
    intro h
    exact hw' (h ▸ w.2)

theorem map_ideleAt (v : HeightOneSpectrum (𝓞 E)) [Fintype (v.Extension (𝓞 K))] (x : (v.adicCompletion E)ˣ) :
    Units.map (genuineβ E K : AdeleRing (𝓞 E) E →* AdeleRing (𝓞 K) K) (ideleAt E v x) =
      ∏ w : v.Extension (𝓞 K), ideleAt K w.1 (upAt E K v w x) := by
  apply Units.ext
  rw [Units.coe_map, Units.coe_prod]
  simp only [val_ideleAt]
  refine Prod.ext ?_ ?_
  · calc ((genuineβ E K : AdeleRing (𝓞 E) E →* AdeleRing (𝓞 K) K)
          ((1 : InfiniteAdeleRing E), ((localUnit (𝓞 E) E v x : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E))).1
        = 1 := by rw [MonoidHom.coe_coe, genuineβ_fst, map_one]
      _ = ∏ w : v.Extension (𝓞 K), (((1 : InfiniteAdeleRing K),
            ((localUnit (𝓞 K) K w.1 (upAt E K v w x) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K))).1 := by
          simp
      _ = _ := Prod.fst_prod.symm
  · calc ((genuineβ E K : AdeleRing (𝓞 E) E →* AdeleRing (𝓞 K) K)
          ((1 : InfiniteAdeleRing E), ((localUnit (𝓞 E) E v x : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E))).2
        = finiteConorm (𝓞 E) E K (𝓞 K) ((localUnit (𝓞 E) E v x : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) := by
          rw [MonoidHom.coe_coe, genuineβ_snd]
      _ = ∏ w : v.Extension (𝓞 K), (((1 : InfiniteAdeleRing K),
            ((localUnit (𝓞 K) K w.1 (upAt E K v w x) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K))).2 :=
          finiteConorm_localUnit E K v x
      _ = _ := Prod.snd_prod.symm

theorem localChar_restrict (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    ((localChar (restrict E K μ) v x : ℂˣ) : ℂ) =
      ∏ᶠ w : v.Extension (𝓞 K), ((localChar μ w.1
        (Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion K)).toMonoidHom x) : ℂˣ) : ℂ) := by
  classical
  haveI : Fintype (v.Extension (𝓞 K)) := HeightOneSpectrum.Extension.fintype (𝓞 E) E K (𝓞 K) v
  rw [finprod_eq_prod_of_fintype, localChar_eq, restrict_apply, map_ideleAt, map_prod, Units.coe_prod]
  rfl

theorem main (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsIdeleClassChar (𝓞 K) K μ) (hcont : Continuous μ) :
    ∃ ν : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ, IsIdeleClassChar (𝓞 E) E ν ∧ Continuous ν ∧
      ∀ (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ),
        ((localChar ν v x : ℂˣ) : ℂ) =
          ∏ᶠ w : v.Extension (𝓞 K), ((localChar μ w.1
            (Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion K)).toMonoidHom x) : ℂˣ) : ℂ) :=
  ⟨restrict E K μ, isIdeleClassChar_restrict E K μ hμ, continuous_restrict E K μ hcont, localChar_restrict E K μ⟩

end NumberField.TateGlobal.WfRestrict

end

open IsDedekindDomain _root_.NumberField _root_.P2MW.S_NumberField_TateGlobal_exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap.NumberField _root_.NumberField.TateGlobal _root_.P2MW.S_NumberField_TateGlobal_exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap.NumberField.TateGlobal NumberField.AdelicLevel AutomorphicForm in

theorem solution
    (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] [Algebra E K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsIdeleClassChar (𝓞 K) K μ) (hcont : Continuous μ) :
    ∃ ν : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ, IsIdeleClassChar (𝓞 E) E ν ∧ Continuous ν ∧
      ∀ (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ),
        ((localChar ν v x : ℂˣ) : ℂ) =
          ∏ᶠ w : v.Extension (𝓞 K), ((localChar μ w.1
            (Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion K)).toMonoidHom x) : ℂˣ) : ℂ) :=
  NumberField.TateGlobal.WfRestrict.main E K μ hμ hcont

end S_NumberField_TateGlobal_exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap (solution)
