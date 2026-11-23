-- Prove2me | solution 1 for Nary.restrict_if
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:38:43.451792+00:00
-- url     : https://prove2.me/submissions/c840578d-512c-4d03-bc03-e1fa41f09be8

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_Nary

set_option autoImplicit true
open Nary
namespace Nary
theorem _root_.solution {c : Func n α Bool} :
    restrict (fun I ↦ if c I then f I else g I) b i =
    fun I ↦ if (restrict c b i I) then (restrict f b i I) else (restrict g b i I) :=
  funext (fun _ ↦ rfl)
end Nary
