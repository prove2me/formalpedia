-- Prove2me | solution 1 for GroupCohomology.RepImage.seq_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/172acc57-bb81-5aa5-ad24-e9563916e0e1

import Mathlib
import Definitions.Def_GroupCohomology_RepCokernel
import Definitions.Def_GroupCohomology_RepImage
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GroupCohomology_RepImage_seq_shortExact

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open CategoryTheory

namespace Rep p2m_export "Rep" "of epi_iff_surjective mono_iff_injective" end Rep
p2m_open_scoped "Rep" in

theorem Rep.shortExact_of_hom'' {k G : Type} [CommRing k] [Group G] {S : ShortComplex (Rep k G)}
    (hf : Function.Injective S.f.hom) (hg : Function.Surjective S.g.hom)
    (hfg : ∀ y : S.X₂, S.g.hom y = 0 ↔ y ∈ Set.range S.f.hom) : S.ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ((Rep.mono_iff_injective _).2 hf) ((Rep.epi_iff_surjective _).2 hg)
  refine Functor.reflects_exact_of_faithful (forget₂ (Rep k G) (ModuleCat k)) _ ?_
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  intro y
  exact hfg y

theorem solution {k G : Type} [CommRing k] [Group G] {X Y : Rep k G} (f : X ⟶ Y) :
    (GroupCohomology.RepImage.seq f).ShortExact := by
  refine Rep.shortExact_of_hom'' (GroupCohomology.RepImage.ι_hom_injective f) (GroupCohomology.RepCokernel.π_hom_surjective f) ?_
  intro y
  change (GroupCohomology.RepCokernel.π f).hom y = 0 ↔ y ∈ Set.range (GroupCohomology.RepImage.ι f).hom
  rw [GroupCohomology.RepCokernel.π_hom_apply_eq_zero_iff]
  constructor
  · intro hy
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact x.2

end S_GroupCohomology_RepImage_seq_shortExact
end P2MW
export P2MW.S_GroupCohomology_RepImage_seq_shortExact (solution)
