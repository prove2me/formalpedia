-- Prove2me | solution 1 for HadwigerMader.colorable_three_of_not_isMinor_K4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:52:53.15374+00:00
-- url     : https://prove2.me/submissions/a8e76c85-fd3b-46d1-a736-2d9c812e9f75

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Definitions.Def_HadwigerMader_Solution
public import Theorems.Thm_HadwigerMader_isMinor_iff_lib
public import Theorems.Thm_CliqueMinors_colorable_three_of_not_isMinor_K4


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open HadwigerMader
variable {V W : Type*}
namespace HadwigerMader
theorem _root_.solution [Finite V] (G : SimpleGraph V)
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) : G.Colorable 3 :=
  CliqueMinors.colorable_three_of_not_isMinor_K4 G
    (fun h' => h ((isMinor_iff_lib _ G).2 h'))
end HadwigerMader
