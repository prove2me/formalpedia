-- Prove2me | solution 1 for HorizontalPadicL.SeedCyclotomicGaloisCharacterDataV2.exists_fullOrder_value_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T11:47:23.759387+00:00
-- url     : https://prove2.me/submissions/7e21a5fb-c56c-4fb1-97e7-c49eae9feb07

import Definitions.Def_KN_SeedCyclotomicGaloisCharactersV3B

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

theorem _root_.solution
    {N p m : ℕ} [Fact p.Prime]
    (η : DirichletCharacterWithLevel)
    (C : SeedCyclotomicGaloisCharacterDataV2 N p m η) :
    ∃ a : (ZMod η.1.1)ˣ,
      orderOf (η.2 (a : ZMod η.1.1)) = orderOf η.2 := by
  obtain ⟨a, ha⟩ := C.only_seed_values C.seedGenerator
  refine ⟨a, ?_⟩
  rw [← C.seedGenerator_order, ← orderOf_units]
  exact congrArg orderOf ha.symm

end HorizontalPadicL
