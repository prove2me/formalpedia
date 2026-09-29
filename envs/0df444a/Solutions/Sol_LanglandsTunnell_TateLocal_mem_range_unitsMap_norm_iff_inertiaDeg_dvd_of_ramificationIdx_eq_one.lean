-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.mem_range_unitsMap_norm_iff_inertiaDeg_dvd_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c0843af2-e210-539d-97f5-947d90c4b67b

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one
import Theorems.Thm_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_mem_range_unitsMap_norm_iff_inertiaDeg_dvd_of_ramificationIdx_eq_one

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace N0cg

variable (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))

theorem valued_norm_eq_exp_mul {y : w.1.adicCompletion M} {n : ℤ}
    (hy : Valued.v y = WithZero.exp n) :
    Valued.v (Algebra.norm (v.adicCompletion E) y) =
      WithZero.exp ((Ideal.inertiaDeg' v.asIdeal w.1.asIdeal : ℤ) * n) := by
  rw [M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg E M v w y, hy, ← WithZero.exp_nsmul,
    nsmul_eq_mul]

end N0cg

theorem solution
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1)
    (x : (v.adicCompletion E)ˣ) :
    x ∈ (Units.map (Algebra.norm (v.adicCompletion E) (S := w.1.adicCompletion M) :
        w.1.adicCompletion M →* v.adicCompletion E)).range ↔
      ∃ k : ℤ, Valued.v (x : v.adicCompletion E) =
        WithZero.exp ((Ideal.inertiaDeg' v.asIdeal w.1.asIdeal : ℤ) * k) := by
  constructor
  ·
    rintro ⟨y, rfl⟩
    have hy0 : Valued.v (y : w.1.adicCompletion M) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr y.ne_zero
    refine ⟨WithZero.log (Valued.v (y : w.1.adicCompletion M)), ?_⟩
    rw [Units.coe_map]
    exact N0cg.valued_norm_eq_exp_mul E M v w (WithZero.exp_log hy0).symm
  ·
    rintro ⟨k, hk⟩
    obtain ⟨y₀, hy₀⟩ := valuedAdicCompletion_surjective M w.1 (WithZero.exp k)
    have hNy₀ := N0cg.valued_norm_eq_exp_mul E M v w hy₀
    have hy₀ne : y₀ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy₀
      exact WithZero.exp_ne_zero hy₀.symm
    set y₀u : (w.1.adicCompletion M)ˣ := Units.mk0 y₀ hy₀ne with hy₀u
    set N := (Units.map (Algebra.norm (v.adicCompletion E) (S := w.1.adicCompletion M) :
        w.1.adicCompletion M →* v.adicCompletion E)) with hNdef
    have hu : x / N y₀u ∈ LanglandsTunnell.TateLocal.higherUnitsAt E v 0 := by
      rw [LanglandsTunnell.TateLocal.mem_higherUnitsAt_zero_iff]
      rw [Units.val_div_eq_div_val, map_div₀, hk, hNdef, Units.coe_map, hy₀u, Units.val_mk0, hNy₀,
        div_self WithZero.exp_ne_zero]
    rw [← LanglandsTunnell.TateLocal.image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one E M v w he 0] at hu
    obtain ⟨u, -, hu⟩ := hu
    exact ⟨u * y₀u, by rw [map_mul, hu, div_mul_cancel]⟩

end S_LanglandsTunnell_TateLocal_mem_range_unitsMap_norm_iff_inertiaDeg_dvd_of_ramificationIdx_eq_one
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_mem_range_unitsMap_norm_iff_inertiaDeg_dvd_of_ramificationIdx_eq_one (solution)
