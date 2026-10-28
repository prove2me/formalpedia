-- Prove2me | solution 1 for OAI.Kadison.InfiniteAmplification.stable_center_range
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:27:10.434655+00:00
-- url     : https://prove2.me/submissions/78685552-402e-4f08-aed5-8c0061aa5a27

import Mathlib
import Definitions.Def_OAIQ039C027
import Definitions.Def_OAIQ039C031

section
-- module Solutions.OAIQ039_CM.Commutator_InfiniteCenter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

namespace Kadison.InfiniteAmplification

local instance infiniteCenterDecidableEq_rfa939e_1 {α : Sort*} : DecidableEq α := Classical.decEq α
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma map_injective : Function.Injective (map (ι:=ℕ) (H:=H) (G:=H)) := by
  intro S T h
  ext x
  have he := congrArg (fun R : Space ℕ H →L[ℂ] Space ℕ H => R (lp.single 2 0 x) 0) h
  simpa only [map_apply,lp.single_apply,Pi.single_eq_same] using he

lemma mem_algebra (M : VonNeumannAlgebra H) (T : Space ℕ H →L[ℂ] Space ℕ H) :
    T∈algebra M ↔ ∃ a : M,map (a : H →L[ℂ] H)=T := Iff.rfl

lemma map_mem_algebra (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) (ha : a∈M) :
    map (ι:=ℕ) a∈algebra M := ⟨⟨a,ha⟩,rfl⟩

lemma map_mem_center (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    map (ι:=ℕ) a∈CentralCorner.center (algebra M) ↔ a∈CentralCorner.center M := by
  rw [CentralCorner.mem_center,CentralCorner.mem_center]
  constructor
  · rintro ⟨⟨b,hb⟩,hc⟩
    have hba : (b:H →L[ℂ] H)=a := map_injective hb
    refine ⟨hba ▸ b.property,?_⟩
    intro c hc'
    apply map_injective
    change diagonal (ι:=ℕ) (H:=H) (c*a)=diagonal (ι:=ℕ) (H:=H) (a*c)
    rw [map_mul,map_mul]
    exact hc (map c) (map_mem_algebra M c hc')
  · rintro ⟨ha,hc⟩
    refine ⟨map_mem_algebra M a ha,?_⟩
    rintro _ ⟨b,rfl⟩
    change diagonal (ι:=ℕ) (H:=H) b.val*diagonal (ι:=ℕ) (H:=H) a=
      diagonal (ι:=ℕ) (H:=H) a*diagonal (ι:=ℕ) (H:=H) b.val
    rw [←map_mul,←map_mul,hc b b.property]

lemma center_range (M : VonNeumannAlgebra H) (T : Space ℕ H →L[ℂ] Space ℕ H)
    (hT : T∈CentralCorner.center (algebra M)) :
    ∃ a : CentralCorner.center M,map (a : H →L[ℂ] H)=T := by
  obtain ⟨a,rfl⟩ := (mem_algebra M T).mp ((CentralCorner.mem_center _ _).mp hT).1
  exact ⟨⟨a,(map_mem_center M a).mp hT⟩,rfl⟩

end Kadison.InfiniteAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryCenterTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

namespace Kadison.UnitaryTransport

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (U : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)

lemma mem_center_algebra (a : H →L[ℂ] H) :
    U.conjStarAlgEquiv a∈CentralCorner.center (algebra U M) ↔ a∈CentralCorner.center M := by
  rw [CentralCorner.mem_center,CentralCorner.mem_center,mem_algebra]
  constructor
  · rintro ⟨ha,hc⟩
    refine ⟨ha,?_⟩
    intro b hb
    apply U.conjStarAlgEquiv.injective
    rw [map_mul,map_mul]
    exact hc _ ((mem_algebra U M b).mpr hb)
  · rintro ⟨ha,hc⟩
    refine ⟨ha,?_⟩
    rintro _ ⟨b,hb,rfl⟩
    change U.conjStarAlgEquiv b*U.conjStarAlgEquiv a=U.conjStarAlgEquiv a*U.conjStarAlgEquiv b
    rw [←map_mul,←map_mul,hc b hb]

lemma center_range (Z : K →L[ℂ] K) (hZ : Z∈CentralCorner.center (algebra U M)) :
    ∃ T : H →L[ℂ] H,T∈CentralCorner.center M ∧ U.conjStarAlgEquiv T=Z := by
  obtain ⟨T,rfl⟩ := U.conjStarAlgEquiv.surjective Z
  exact ⟨T,(mem_center_algebra U M T).mp hZ,rfl⟩

end Kadison.UnitaryTransport

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StableCenterRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

namespace Kadison.InfiniteAmplification

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma stable_center_range_oai (M : VonNeumannAlgebra H) (U : Space ℕ H ≃ₗᵢ[ℂ] K)
    (Z : K →L[ℂ] K) (hZ : Z∈CentralCorner.center (UnitaryTransport.algebra U (algebra M))) :
    ∃ a : CentralCorner.center M,U.conjStarAlgEquiv (map a.val)=Z := by
  obtain ⟨T,hT,hTZ⟩ := UnitaryTransport.center_range U (algebra M) Z hZ
  obtain ⟨a,ha⟩ := center_range M T hT
  exact ⟨a,by rw [ha]; exact hTZ⟩

end Kadison.InfiniteAmplification

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.InfiniteAmplification.stable_center_range_oai.{u_1, u_2} := @OAI.Kadison.InfiniteAmplification.stable_center_range_oai.{u_1, u_2}
